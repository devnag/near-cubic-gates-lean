import Proof.Gates.CounterMachine.FormulaLin

/-! # RG machine, part 7: cost classes of the token printers

Polynomial bounds `K·(Λ+1)^d` for the printers of parts 2–3, in a size parameter `Λ` that bounds every register value,
every bit length and every list length the printer touches (`sec:prelim`, "Machine model": fixed polynomial factors). -/

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord)

theorem sum_map_le {α : Type} (xs : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x ∈ xs, f x ≤ B) :
    (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    nlinarith

theorem intWord_length_le (z : ℤ) : (Interfaces.intWord z).length ≤ 2 * natBitLength z.natAbs + 5 := by
  have hs : natBitLength (if z < 0 then 1 else 0) ≤ 1 := by split_ifs <;> simp [natBitLength]
  simp only [Interfaces.intWord, List.length_append, natWord_length']
  omega

theorem printCost_le (x Λ : ℕ) (hx : x ≤ Λ) : printCost x ≤ 2300 * (Λ + 1) ^ 2 := by
  have hb := nbl_le x
  unfold printCost
  have h1 : (natBitLength x + 10) * (100 * x + 200) ≤ (11 * (Λ + 1)) * (200 * (Λ + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem linBodyCost_le (z : ℤ) (x Λ : ℕ) (hz : natBitLength z.natAbs ≤ Λ) (hx : x ≤ Λ) :
    linBodyCost z x ≤ 3100 * (Λ + 1) ^ 2 := by
  have h1 := printCost_le x Λ hx
  have h2 := intWord_length_le z
  have e0 : (natWord 0).length = 3 := by decide
  have e1 : (natWord 1).length = 3 := by decide
  have e2 : (tokWord .mul).length = 7 := by decide
  unfold linBodyCost
  rw [e0, e1, e2]
  nlinarith

/-- **The linear-form printer's class.** -/
theorem linCost_le (o : ℕ) (as : List ℤ) (Λ : ℕ) (hlen : o + as.length ≤ Λ)
    (hz : ∀ a ∈ as, natBitLength a.natAbs ≤ Λ) : linCost o as ≤ 3300 * (Λ + 1) ^ 3 := by
  have hs := sum_map_le (List.range as.length)
    (fun i => linBodyCost (as.getD (0 + i) 0) (o + (0 + i)) + 4) (3104 * (Λ + 1) ^ 2) (by
      intro i hi
      simp only [List.mem_range] at hi
      have hg : natBitLength (as.getD (0 + i) 0).natAbs ≤ Λ := by
        rw [Nat.zero_add, List.getD_eq_getElem _ _ hi]; exact hz _ (List.getElem_mem hi)
      have := linBodyCost_le (as.getD (0 + i) 0) (o + (0 + i)) Λ hg (by omega)
      have : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega)
  rw [List.length_range] at hs
  have e0 : (tokWord (.const 0)).length = 9 := by decide
  have e1 : (tokWord .add).length = 5 := by decide
  unfold linCost
  rw [e0, e1]
  have hm : as.length ≤ Λ + 1 := by omega
  have h3 : as.length * (3104 * (Λ + 1) ^ 2) ≤ (Λ + 1) * (3104 * (Λ + 1) ^ 2) := Nat.mul_le_mul_right _ hm
  nlinarith

end NearCubicGates.Close.CounterMachine
