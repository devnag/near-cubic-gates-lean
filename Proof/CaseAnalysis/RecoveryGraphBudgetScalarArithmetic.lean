import Proof.CaseAnalysis.RecoveryGraphBudgetSupport

/-! Keep the paid machine budget opaque in the final degree-48 arithmetic. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem serializer_arithmetic (F A X cost : ℕ) (hX : 1 ≤ X)
    (hf : F ≤ A*X^4) (hc : cost ≤ 6*F+8+1000000000064*(F+1)^12) :
    cost ≤ (6*A+8+1000000000064*(A+1)^12)*X^48 := by
  have h4 : 1 ≤ X^4 := Nat.one_le_pow _ _ hX
  have h48 : 1 ≤ X^48 := Nat.one_le_pow _ _ hX
  have hpower : X^4 ≤ X^48 := Nat.pow_le_pow_right (by omega) (by decide)
  have hsmall : F+1 ≤ (A+1)*X^4 := by
    calc
      _ ≤ A*X^4+X^4 := Nat.add_le_add hf h4
      _ = _ := by ring
  have hpoly := Nat.pow_le_pow_left hsmall 12
  rw [Nat.mul_pow,←Nat.pow_mul] at hpoly
  have hlinear : 6*F+8 ≤ (6*A+8)*X^48 := by
    calc
      _ ≤ 6*(A*X^48)+8*X^48 := Nat.add_le_add
        (Nat.mul_le_mul_left 6 (hf.trans (Nat.mul_le_mul_left A hpower)))
        (by simpa using Nat.mul_le_mul_left 8 h48)
      _ = _ := by ring
  calc
    cost ≤ 6*F+8+1000000000064*(F+1)^12 := hc
    _ ≤ (6*A+8)*X^48+1000000000064*((A+1)^12*X^48) :=
      Nat.add_le_add hlinear (Nat.mul_le_mul_left 1000000000064 hpoly)
    _ = _ := by ring

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
