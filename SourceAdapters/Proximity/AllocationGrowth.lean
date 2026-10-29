import SourceAdapters.Proximity.SourceGrowth

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the actual paid logarithmic prefix provides a
single polynomial allocation for widths, call lengths and call clocks. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open Growth

def allocation (A D : ℕ) (S : SourceCircuit) : ℕ :=
  2 ^ (D * leadOnes (LengthPrefix.wrapped (sourceCircuitWord S))) * A

def uniformSize (A D : ℕ) : Sz := ⟨A, D, A, D, A, D⟩

theorem allocation_covers (A D : ℕ) (S : SourceCircuit) :
    A * (sourceMeasure S + 1) ^ D ≤ allocation A D S := by
  have hl := LengthPrefix.allocation_covers_length (sourceCircuitWord S)
  change sourceMeasure S < 2 ^ leadOnes (LengthPrefix.wrapped (sourceCircuitWord S)) at hl
  have hp := Nat.pow_le_pow_left (by omega : sourceMeasure S + 1 ≤
    2 ^ leadOnes (LengthPrefix.wrapped (sourceCircuitWord S))) D
  unfold allocation
  rw [Nat.mul_comm D, pow_mul]
  simpa only [Nat.mul_comm A] using Nat.mul_le_mul_left A hp

theorem allocation_bounded (A D : ℕ) : Bounded sourceMeasure (allocation A D) :=
  ⟨A * 2 ^ D, D, fun S => LengthPrefix.allocation_bound A D (sourceCircuitWord S)⟩

theorem allocation_positive (A D : ℕ) (hA : 1 ≤ A) (S : SourceCircuit) : 1 ≤ allocation A D S := by
  have hp : 1 ≤ 2 ^ (D * leadOnes (LengthPrefix.wrapped (sourceCircuitWord S))) := Nat.one_le_pow _ _ (by decide)
  exact (Nat.mul_le_mul hp hA)

theorem sufficient_allocation {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (a K e : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 (sourceMeasure S + 2)) :
    ∃ A D : ℕ, 1 ≤ A ∧ ∀ S,
      widthDemand q (sourceMeasure S) (V S).randomBits (callBudgetCap q a K e (sourceMeasure S)) ≤ allocation A D S ∧
      requestCap q a (sourceMeasure S) ≤ allocation A D S ∧
      callBudgetCap q a K e (sourceMeasure S) ≤ allocation A D S := by
  obtain ⟨A, D, h⟩ := (((widthDemand_bounded V a hr K e).add (requestCap_bounded q a)).add
    (callBudgetCap_bounded q a K e)).add (bounded_const 1)
  refine ⟨A + 1, D, by omega, fun S => ?_⟩
  have hs := (h S).trans (allocation_covers A D S)
  have ha : allocation A D S ≤ allocation (A + 1) D S := Nat.mul_le_mul_left _ (by omega)
  have hh := hs.trans ha
  dsimp only at hh
  exact ⟨by omega, by omega, by omega⟩

end NearCubicGates.Adapters.Proximity.SourceCallee
