import SourceAdapters.ShortPCP.TimeRecursion
import Mathlib.LinearAlgebra.Lagrange

/-!
# Single-run time, reference layer 4: the base-case degree test and Lagrange evaluation

The base cases of `D_{RS,=}` (`κ ≤ κ0`) and of `D_RS` (`κ ≤ η`) accept iff the answers on the `2^κ` points of the
subspace are the values of a polynomial of degree at most `deg` (SubspaceInterp, Algorithm 23, "if d̃ ≤ d output 1";
the leaf's `degreeTest`, a classical `∃`). On an independent basis the points are distinct, so this is decided by
Lagrange interpolation through the first `deg + 1` points and a check at all points (`degreeTestF_eq`): `O(4^κ)`
field operations and `2^κ` inverses. The same evaluator `lagEval` computes the low-degree extension `p_x` of the
instance (proof of `thm:short-pcp-ours`: "By Lagrange interpolation over the subspace `I` of size `|x̄|`, each evaluation takes
`O(|x̄|²)` field operations").
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open Finset Polynomial NearCubicGates.Published.BCGT13

variable {F : Type} [Field F] [DecidableEq F]

/-- Lagrange's formula: the value at `x` of the polynomial of degree `< m` through `(pt j, val j)`, `j < m`. -/
def lagEval (m : ℕ) (pt : ℕ → F) (val : ℕ → F) (x : F) : F :=
  ∑ i ∈ Finset.range m, val i * ∏ j ∈ (Finset.range m).erase i, ((pt i - pt j)⁻¹ * (x - pt j))

omit [DecidableEq F] in
theorem lagEval_eq (m : ℕ) (pt val : ℕ → F) (x : F) :
    lagEval m pt val x = (Lagrange.interpolate (Finset.range m) pt val).eval x := by
  simp [lagEval, Lagrange.interpolate_apply, eval_finsetSum, Lagrange.basis, eval_prod, Lagrange.basisDivisor]

/-- The base-case degree test, poly-time form: all points agree with the interpolant through the first `deg + 1`. -/
def degreeTestF (B : List F) (O : F) (deg : ℕ) (ans : ℕ → F) : Bool :=
  if 2 ^ B.length ≤ deg + 1 then true
  else (List.range (2 ^ B.length)).all fun i =>
    decide (lagEval (deg + 1) (fun j => eltWithIndex B O (j + 1)) (fun j => ans (j + 1))
      (eltWithIndex B O (i + 1)) = ans (i + 1))

omit [DecidableEq F] in
theorem injOn_points [CharP F 2] {B : List F} (hB : Indep B) (O : F) (m : ℕ) (hm : m ≤ 2 ^ B.length) :
    Set.InjOn (fun j => eltWithIndex B O (j + 1)) (Finset.range m) := by
  intro a ha b hb h
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only [eltWithIndex_eq, Nat.add_sub_cancel] at h
  exact hB.injOn (by omega) (by omega) (add_right_cancel h)

omit [DecidableEq F] in
theorem natDegree_interpolate_le [CharP F 2] {B : List F} (hB : Indep B) (O : F) (m : ℕ) (hm : m ≤ 2 ^ B.length)
    (val : ℕ → F) (deg : ℕ) (hd : m ≤ deg + 1) :
    (Lagrange.interpolate (Finset.range m) (fun j => eltWithIndex B O (j + 1)) val).natDegree ≤ deg := by
  have h := Lagrange.degree_interpolate_lt (r := val) (injOn_points hB O m hm)
  rw [Finset.card_range] at h
  rcases eq_or_ne (Lagrange.interpolate (Finset.range m) (fun j => eltWithIndex B O (j + 1)) val) 0 with h0 | h0
  · rw [h0]; simp
  · rw [degree_eq_natDegree h0] at h
    have : (Lagrange.interpolate (Finset.range m) (fun j => eltWithIndex B O (j + 1)) val).natDegree < m := by
      exact_mod_cast h
    omega

/-- **The base-case degree test in poly-time form** (Algorithm 23 with the decision of Algorithm 16 step 1). -/
theorem degreeTestF_eq [CharP F 2] {B : List F} (hB : Indep B) (O : F) (deg : ℕ) (ans : ℕ → F) :
    degreeTestF B O deg ans = degreeTest B O deg ans := by
  unfold degreeTest
  rw [Bool.eq_iff_iff, @decide_eq_true_iff _ (Classical.propDecidable _)]
  unfold degreeTestF
  split_ifs with hN
  · simp only [true_iff]
    refine ⟨Lagrange.interpolate (Finset.range (2 ^ B.length)) (fun j => eltWithIndex B O (j + 1))
      (fun j => ans (j + 1)), natDegree_interpolate_le hB O _ le_rfl _ deg hN, fun i hi => ?_⟩
    have hn := Lagrange.eval_interpolate_at_node (r := fun j => ans (j + 1)) (injOn_points hB O _ le_rfl)
      (Finset.mem_range.mpr hi)
    exact hn
  · push Not at hN
    rw [List.all_eq_true]
    constructor
    · intro h
      refine ⟨Lagrange.interpolate (Finset.range (deg + 1)) (fun j => eltWithIndex B O (j + 1))
        (fun j => ans (j + 1)), natDegree_interpolate_le hB O _ hN.le _ deg le_rfl, fun i hi => ?_⟩
      have := h i (List.mem_range.mpr hi)
      rw [decide_eq_true_iff, lagEval_eq] at this
      exact this
    · rintro ⟨P, hP, hPv⟩ i hi
      rw [List.mem_range] at hi
      have hdeg : P.degree < (Finset.range (deg + 1)).card := by
        rw [Finset.card_range]
        exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le hP)
      have hPeq := Lagrange.eq_interpolate_of_eval_eq (fun j => ans (j + 1)) (injOn_points hB O _ hN.le) hdeg
        (fun j hj => hPv j (by rw [Finset.mem_range] at hj; omega))
      rw [decide_eq_true_iff, lagEval_eq, ← hPeq]
      exact hPv i hi

end NearCubicGates.Adapters.ShortPCP.Time
