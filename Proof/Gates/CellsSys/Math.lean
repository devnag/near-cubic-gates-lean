import Proof.Gates.Cells.SysSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-! ## Constant-radix digits -/

theorem prod_replicate (n w : ℕ) : (List.replicate n w).prod = w ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.prod_cons, ih, pow_succ, mul_comm]

/-- The `i`-th digit (most significant first) of `t` in radix `w` with `n` digits. -/
theorem digitsM_rep_getD (w : ℕ) : ∀ (n t i : ℕ), i < n →
    (digitsM (List.replicate n w) t).getD i 0 = t / w ^ (n - 1 - i) % w
  | 0, _, i, h => absurd h (by omega)
  | n + 1, t, 0, _ => by
    rw [List.replicate_succ, digitsM, List.getD_cons_zero, prod_replicate]
    congr 2
  | n + 1, t, i + 1, h => by
    rw [List.replicate_succ, digitsM, List.getD_cons_succ, digitsM_rep_getD w n t i (by omega)]
    congr 3
    omega

/-! ## Signed pairs -/

/-- The integer of a pair. -/
def zOf (p q : ℕ) : ℤ := (p : ℤ) - q

/-- Floor division of the pair `(Np, Nn)` by `A > 0`, as a pair. -/
def fdivP (Np Nn A : ℕ) : ℕ × ℕ := if Nn ≤ Np then ((Np - Nn) / A, 0) else (0, (Nn - Np + A - 1) / A)

theorem fdivP_eq (Np Nn A : ℕ) (hA : 0 < A) : zOf (fdivP Np Nn A).1 (fdivP Np Nn A).2 = zOf Np Nn / (A : ℤ) := by
  unfold fdivP zOf
  split_ifs with h
  · simp only [Nat.cast_zero, sub_zero]
    rw [show (Np : ℤ) - Nn = ((Np - Nn : ℕ) : ℤ) by push_cast [h]; ring]
    exact (Int.natCast_ediv _ _)
  · simp only [Nat.cast_zero, zero_sub]
    have h1 : Nn - Np ≤ (Nn - Np + A - 1) / A * A := by
      have := Nat.lt_div_mul_add (a := Nn - Np + A - 1) hA
      omega
    have h2 : (Nn - Np + A - 1) / A * A < Nn - Np + A := by
      have := Nat.div_mul_le_self (Nn - Np + A - 1) A
      omega
    have hN : (Np : ℤ) - Nn = -((Nn - Np : ℕ) : ℤ) := by push_cast [show Np ≤ Nn by omega]; ring
    rw [hN]
    have hA' : (0 : ℤ) < A := by exact_mod_cast hA
    have h1' : ((Nn - Np : ℕ) : ℤ) ≤ (((Nn - Np + A - 1) / A : ℕ) : ℤ) * A := by exact_mod_cast h1
    have h2' : (((Nn - Np + A - 1) / A : ℕ) : ℤ) * A < ((Nn - Np : ℕ) : ℤ) + A := by exact_mod_cast h2
    have key := (Int.ediv_emod_unique (a := -((Nn - Np : ℕ) : ℤ)) (b := (A : ℤ))
      (q := -(((Nn - Np + A - 1) / A : ℕ) : ℤ)) (r := (A : ℤ) * (((Nn - Np + A - 1) / A : ℕ) : ℤ) - ((Nn - Np : ℕ) : ℤ))
      hA').2 ⟨by ring, by nlinarith, by nlinarith⟩
    rw [key.1]

end NearCubicGates.Close.Cells
