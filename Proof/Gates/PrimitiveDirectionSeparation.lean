import Proof.Gates.TomographyDirections
import Mathlib.Tactic.Linarith

/-! Distinct positive primitive directions cannot have the same slope. -/

set_option autoImplicit false

namespace NearCubicGates.PrimitiveDirectionSeparation

theorem coprime_same_slope (α β a b : ℕ) (_hα : 0 < α) (hβ : 0 < β)
    (hc : α.Coprime β) (hab : a.Coprime b) (h : α * b = a * β) :
    α = a ∧ β = b := by
  have hdvd : β ∣ b := hc.symm.dvd_of_dvd_mul_left (by rw [h]; exact dvd_mul_left β a)
  obtain ⟨t, ht⟩ := hdvd
  have ha : a = α * t := by nlinarith
  have hg : t = 1 := by
    have hs := hab.gcd_eq_one
    rw [ha, ht, Nat.gcd_mul_right, hc.gcd_eq_one, one_mul] at hs
    exact hs
  simp only [hg, mul_one] at ht ha
  exact ⟨ha.symm, ht.symm⟩

theorem shell_coprime (m : ℕ) {a : ℕ} (ha : a ∈ TomographyDirections.shell m) :
    a.Coprime (m - a) := by
  have ham : a.Coprime m := (Finset.mem_filter.mp ha).2.symm
  exact (Nat.coprime_sub_self_right (Nat.le_of_lt (Finset.mem_range.mp
    (Finset.mem_filter.mp ha).1))).mpr ham

theorem distinct_shell_determinant (m n a b : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (ha : a ∈ TomographyDirections.shell m) (hb : b ∈ TomographyDirections.shell n)
    (hne : (m, a) ≠ (n, b)) : (n - b) * a ≠ b * (m - a) := by
  intro heq
  have haBounds := TomographyDirections.shell_bounds m hm ha
  have hbBounds := TomographyDirections.shell_bounds n hn hb
  have hs := coprime_same_slope a (m - a) b (n - b) haBounds.1 (by omega)
    (shell_coprime m ha) (shell_coprime n hb) (by nlinarith)
  apply hne
  apply Prod.ext <;> omega

end NearCubicGates.PrimitiveDirectionSeparation
