import Proof.Supplier.SupplierTouching
import Mathlib.Data.Nat.Choose.Bounds

/-! Coarse arithmetic bounds for the paper's unchanged touching selector.
They permit a full Pascal table and ordinary fixed-width arithmetic without
factorials, division, or a logarithmic-width argument. This file does not
claim to supply the physical table, lookup, or selector program. -/
namespace NearCubicWires.RepairSource.CloseoutTouchingArithmetic
open SupplierTouching
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem binomial_fits (q m k : ℕ) (hm : m ≤ q) : Nat.choose m k < 2^(q+1) := by
  have h := (Nat.choose_le_two_pow m k).trans (Nat.pow_le_pow_right (by decide : 0 < 2) hm)
  have hp : 0 < 2^q := by positivity
  rw [pow_succ]
  omega

theorem numerator_bound {q : ℕ} {Gate : Type} [Fintype Gate]
    (support : Gate → Finset (Fin q)) (selected undecided : Finset (Fin q)) (k : ℕ) :
    conditionalTouchNumerator support selected undecided k ≤ Fintype.card Gate * 2^q := by
  classical
  have hu : undecided.card ≤ q := (Finset.card_le_univ undecided).trans_eq (Fintype.card_fin q)
  have hc := (Nat.choose_le_two_pow undecided.card k).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hu)
  calc
    conditionalTouchNumerator support selected undecided k ≤ ∑ _ : Gate, 2^q := by
      apply Finset.sum_le_sum
      intro gate _
      unfold conditionalGateTouchCount
      split <;> omega
    _ = Fintype.card Gate * 2^q := by simp

theorem comparison_product_fits {q : ℕ} {Gate : Type} [Fintype Gate]
    (support : Gate → Finset (Fin q)) (selected undecided : Finset (Fin q))
    (k m j : ℕ) (hm : m ≤ q) :
    conditionalTouchNumerator support selected undecided k * Nat.choose m j <
      2^(Fintype.card Gate + 2*q) := by
  have hn := numerator_bound support selected undecided k
  have hc := (Nat.choose_le_two_pow m j).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hm)
  have hg : Fintype.card Gate < 2^Fintype.card Gate := Nat.lt_two_pow_self
  calc
    _ ≤ (Fintype.card Gate * 2^q) * 2^q := Nat.mul_le_mul hn hc
    _ = Fintype.card Gate * 2^(2*q) := by rw [two_mul, pow_add]; ring
    _ < 2^Fintype.card Gate * 2^(2*q) := Nat.mul_lt_mul_of_pos_right hg (by positivity)
    _ = _ := (pow_add _ _ _).symm

end NearCubicWires.RepairSource.CloseoutTouchingArithmetic
