import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact directional degree count for two-score tomography

This proves the arithmetic identity in the final paragraph of `lem:two-window`.
It does not assume an asymptotic totient estimate or binomial divisibility.
-/

namespace NearCubicGates.TomographyDirections

open scoped BigOperators

/-- At norm `m`, the positive primitive choices are `a` coprime to `m`. -/
def shell (m : ℕ) : Finset ℕ := (Finset.range m).filter (fun a => m.Coprime a)

theorem shell_card (m : ℕ) : (shell m).card = Nat.totient m := rfl

theorem shell_bounds (m : ℕ) (hm : 2 ≤ m) {a : ℕ} (ha : a ∈ shell m) :
    0 < a ∧ a < m := by
  obtain ⟨hlt, hco⟩ := Finset.mem_filter.mp ha
  have hlt' := Finset.mem_range.mp hlt
  have hne : a ≠ 0 := by
    intro h
    subst a
    have h : m = 1 := by simpa [Nat.Coprime] using hco
    omega
  exact ⟨Nat.pos_of_ne_zero hne, hlt'⟩

theorem shell_reflect (m : ℕ) (hm : 2 ≤ m) {a : ℕ} (ha : a ∈ shell m) :
    m - a ∈ shell m := by
  have hab := shell_bounds m hm ha
  obtain ⟨_, hco⟩ := Finset.mem_filter.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
  exact (Nat.coprime_self_sub_right (Nat.le_of_lt hab.2)).mpr hco

theorem shell_reflection_sum (m : ℕ) (hm : 2 ≤ m) :
    (∑ a ∈ shell m, (m - a)) = ∑ a ∈ shell m, a := by
  apply Finset.sum_bij (fun a _ => m - a)
  · intro a ha
    exact shell_reflect m hm ha
  · intro a ha b hb hab
    have ha' := shell_bounds m hm ha
    have hb' := shell_bounds m hm hb
    omega
  · intro b hb
    refine ⟨m - b, shell_reflect m hm hb, ?_⟩
    have hb' := shell_bounds m hm hb
    omega
  · intro a _
    rfl

/-- The two signs of the nonzero second coordinate together contribute
`m * totient m` to the first-variable degree. -/
theorem shell_degree_sum (m : ℕ) (hm : 2 ≤ m) :
    2 * (∑ a ∈ shell m, (m - a)) = m * Nat.totient m := by
  have hsum : (∑ a ∈ shell m, a) + (∑ a ∈ shell m, (m - a)) =
      m * Nat.totient m := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ a ∈ shell m, (a + (m - a))) = ∑ _a ∈ shell m, m := by
        apply Finset.sum_congr rfl
        intro a ha
        have hb := shell_bounds m hm ha
        omega
      _ = m * Nat.totient m := by simp [shell_card, Nat.mul_comm]
  rw [← shell_reflection_sum m hm] at hsum
  omega

/-- `S(q)` from the quantitative reconstruction criterion, with `S(0)=0`. -/
def degreeSum (q : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 q, m * Nat.totient m

/-- Direct count: the axes contribute one, and every later shell contributes
twice the sum of its absolute second coordinates. -/
def directionalDegree (q : ℕ) : ℕ :=
  if q = 0 then 0 else 1 + ∑ m ∈ Finset.Icc 2 q, 2 * ∑ a ∈ shell m, (m - a)

theorem directionalDegree_eq (q : ℕ) : directionalDegree q = degreeSum q := by
  by_cases hq : q = 0
  · subst q
    simp [directionalDegree, degreeSum]
  · have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hq
    have hI : Finset.Icc 1 q = insert 1 (Finset.Icc 2 q) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    simp only [directionalDegree, if_neg hq, degreeSum, hI]
    rw [Finset.sum_insert (by simp), Nat.totient_one, Nat.mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    exact shell_degree_sum m (Finset.mem_Icc.mp hm).1

end NearCubicGates.TomographyDirections
