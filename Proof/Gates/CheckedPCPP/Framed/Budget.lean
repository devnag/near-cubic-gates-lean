import Proof.Gates.CheckedPCPP.Framed.OutputFree

/-! # Budget forms of the bridge for the Tier-2 literals

The Tier-1 literals state their algorithms as `OrdinaryWordFunction`s with
budgets in the paper's parameters (`K · (X + 1)^e`, or `2^(e·n)` from an onset). The Tier-2
literals state them in Mathlib's model, `TM2ComputableInPolyTime` / `TM2ComputableInTime`, whose
time is a function of the INPUT LENGTH. This module converts, through the output-free bridge
`tm2ToOrdinaryOutputFree` (whose budget is `C · (T + |input| + 1)`):

* `polyEval_le`: `p.eval x ≤ p.eval 1 · (x + 1)^natDegree p` for `p : Polynomial ℕ`.
* `tm2Poly_ordinary`: a polynomial-time TM2 machine whose input words have length at most
  `K₀ · (X a + 1)^a₀` gives an ordinary word function within `K · (X a + 1)^e`.
* `tm2Time_ordinary_le`: the general form, budget `C · (time |ea a| + |ea a| + 1)`.
-/

namespace NearCubicGates.Close.FramedSim
open NearCubicWires
open LocalBitMultitape RepairOrdinary Turing
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- A natural-coefficient polynomial is at most its coefficient sum times `(x + 1)^degree`. -/
theorem polyEval_le (p : Polynomial ℕ) (x : ℕ) :
    p.eval x ≤ p.eval 1 * (x + 1) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [one_pow, Nat.mul_one]
  apply Nat.mul_le_mul_left
  calc x ^ i ≤ (x + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ x) i
    _ ≤ (x + 1) ^ p.natDegree := Nat.pow_le_pow_right (Nat.succ_pos x) hi'

/-- The output-free bridge at an arbitrary larger budget. -/
theorem tm2Time_ordinary_le {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInTime ea eb f) (budget : α → ℕ)
    (hb : ∀ a, simConstant h.tm * (maxStmtSize h.tm + 2) *
      (h.time (ea a).length + (ea a).length + 1) ≤ budget a) :
    Nonempty (RepairSource.OrdinaryWordFunction α ea (fun a => pairs (eb (f a))) budget) :=
  ⟨RepairOrdinary.WordFunction.enlargeBudget (tm2ToOrdinaryOutputFree h) hb⟩

/-- **Polynomial time, polynomial budget.** If the input words have length at most
`K₀ · (X a + 1)^a₀`, a `TM2ComputableInPolyTime` machine yields an ordinary word function within
`K · (X a + 1)^e`. -/
theorem tm2Poly_ordinary {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (X : α → ℕ) (K₀ a₀ : ℕ)
    (hlen : ∀ a, (ea a).length ≤ K₀ * (X a + 1) ^ a₀) :
    ∃ K e : ℕ, Nonempty (RepairSource.OrdinaryWordFunction α ea (fun a => pairs (eb (f a)))
      (fun a => K * (X a + 1) ^ e)) := by
  set d := h.time.natDegree
  set P := h.time.eval 1
  set C := simConstant h.tm * (maxStmtSize h.tm + 2)
  refine ⟨C * (P * (K₀ + 1) ^ d + K₀ + 1), a₀ * d + a₀,
    tm2Time_ordinary_le h.toTM2ComputableInTime _ (fun a => ?_)⟩
  change C * (h.time.eval (ea a).length + (ea a).length + 1) ≤ _
  set N := (ea a).length
  set Y := X a + 1
  have hY : 1 ≤ Y := by omega
  have hN : N ≤ K₀ * Y ^ a₀ := hlen a
  have hYa : 1 ≤ Y ^ a₀ := Nat.one_le_pow _ _ hY
  have hN1 : N + 1 ≤ (K₀ + 1) * Y ^ a₀ := by rw [Nat.add_mul, Nat.one_mul]; omega
  have htime : h.time.eval N ≤ P * ((K₀ + 1) ^ d * Y ^ (a₀ * d)) := by
    calc h.time.eval N ≤ P * (N + 1) ^ d := polyEval_le h.time N
      _ ≤ P * ((K₀ + 1) * Y ^ a₀) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN1 d)
      _ = P * ((K₀ + 1) ^ d * Y ^ (a₀ * d)) := by rw [Nat.mul_pow, ← pow_mul]
  have he1 : Y ^ (a₀ * d) ≤ Y ^ (a₀ * d + a₀) := Nat.pow_le_pow_right hY (by omega)
  have he2 : Y ^ a₀ ≤ Y ^ (a₀ * d + a₀) := Nat.pow_le_pow_right hY (by omega)
  have he3 : 1 ≤ Y ^ (a₀ * d + a₀) := Nat.one_le_pow _ _ hY
  have hsum : h.time.eval N + N + 1 ≤ (P * (K₀ + 1) ^ d + K₀ + 1) * Y ^ (a₀ * d + a₀) := by
    have h1 : P * ((K₀ + 1) ^ d * Y ^ (a₀ * d)) ≤ P * (K₀ + 1) ^ d * Y ^ (a₀ * d + a₀) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ he1
    have h2 : K₀ * Y ^ a₀ ≤ K₀ * Y ^ (a₀ * d + a₀) := Nat.mul_le_mul_left _ he2
    nlinarith
  calc C * (h.time.eval N + N + 1) ≤ C * ((P * (K₀ + 1) ^ d + K₀ + 1) * Y ^ (a₀ * d + a₀)) :=
        Nat.mul_le_mul_left _ hsum
    _ = C * (P * (K₀ + 1) ^ d + K₀ + 1) * Y ^ (a₀ * d + a₀) := (Nat.mul_assoc C _ _).symm

end NearCubicGates.Close.FramedSim
