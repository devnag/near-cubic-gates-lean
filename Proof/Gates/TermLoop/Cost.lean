import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Proof.Gates.TermLoop.Defs

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicGates.Close.WorkerArith (termCost)

theorem poly_bound (tc Z Bc S S' : ℕ) (hS : S' ≤ S) :
    10000 * (S' + 1) ^ 2 + 10 * (10000000000000 * (tc + 1) * (Z + 1) ^ 4 * (Bc + 1)) + 2400 * (Z + 1) +
        100 * (Z + S + 1) + 20 ≤
      1000000000000000 * (tc + 1) * (Z + S + 1) ^ 4 * (Bc + 1) := by
  have hZA : Z + 1 ≤ Z + S + 1 := by omega
  have hSA : S' + 1 ≤ Z + S + 1 := by omega
  have hA1 : 1 ≤ Z + S + 1 := by omega
  have p1 : (Z + 1) ^ 4 ≤ (Z + S + 1) ^ 4 := Nat.pow_le_pow_left hZA 4
  have p2 : (S' + 1) ^ 2 ≤ (Z + S + 1) ^ 2 := Nat.pow_le_pow_left hSA 2
  have p3 : (Z + S + 1) ^ 2 ≤ (Z + S + 1) ^ 4 := Nat.pow_le_pow_right hA1 (by norm_num)
  have p4 : (Z + S + 1) ≤ (Z + S + 1) ^ 4 := by
    calc (Z + S + 1) = (Z + S + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hA1 (by norm_num)
  have q1 : (tc + 1) * (Z + 1) ^ 4 * (Bc + 1) ≤ (tc + 1) * (Z + S + 1) ^ 4 * (Bc + 1) := by gcongr
  have q2 : (Z + S + 1) ^ 4 ≤ (tc + 1) * (Z + S + 1) ^ 4 * (Bc + 1) := by
    have : 1 ≤ (tc + 1) * (Bc + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  nlinarith [q1, q2, p2, p3, p4]

theorem sum_fin10 (f : Fin 10 → ℕ) :
    ∑ t : Fin 10, f t = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]
  rfl

/-- The cost sum with the polynomial parts abstracted. -/
theorem cost_core (A G F K Z S b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : ℕ)
    (h : F + 10 * A + 2400 * (Z + 1) + 100 * (Z + S + 1) + 20 ≤ G) :
    F + 1 + (200 * (Z + 1) + 1 +
      (A + K * b0 + 200 * (Z + 1) + 1 +
      (A + K * b1 + 200 * (Z + 1) + 1 +
      (A + K * b2 + 200 * (Z + 1) + 1 +
      (A + K * b3 + 200 * (Z + 1) + 1 +
      (A + K * b4 + 200 * (Z + 1) + 1 +
      (A + K * b5 + 200 * (Z + 1) + 1 +
      (A + K * b6 + 200 * (Z + 1) + 1 +
      (A + K * b7 + 200 * (Z + 1) + 1 +
      (A + K * b8 + 200 * (Z + 1) + 1 +
      (A + K * b9 + 200 * (Z + 1) + 1 +
      100 * (Z + S + 1)))))))))))) ≤
    G + K * (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9) := by
  simp only [Nat.mul_add]
  omega

theorem gadget_cost_le (tc Z Bc S S' : ℕ) (hS : S' ≤ S) (b : Fin 10 → ℕ) :
    CheckedPCPP.ClauseFront.frontCost S' + 1 + (200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 0) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 1) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 2) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 3) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 4) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 5) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 6) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 7) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 8) + 200 * (Z + 1) + 1 +
      (termCost tc Z Bc (b 9) + 200 * (Z + 1) + 1 +
      100 * (Z + S + 1)))))))))))) ≤
    gadgetCost tc Z Bc S (∑ t : Fin 10, b t) := by
  rw [sum_fin10]
  exact cost_core _ _ _ _ Z S _ _ _ _ _ _ _ _ _ _ (poly_bound tc Z Bc S S' hS)

end NearCubicGates.Close.TermLoop
