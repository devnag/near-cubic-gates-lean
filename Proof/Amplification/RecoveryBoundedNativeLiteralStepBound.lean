import Proof.Amplification.RecoveryBoundedNativeLiteralStepRun

/-! One shared retained capacity discharges every printing, reference, reset
and increment premise of the actual reusable grammar-literal body. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStep
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (index position C : ℕ) (negative : Bool)
    (hi : PCPPNativeSumAppend.budget 0 index+1 ≤ C)
    (hp : PCPPNativeSumAppend.budget 0 position+1 ≤ C)
    (hz : PCPPNativeSumAppend.budget 0 0+1 ≤ C)
    (hindex : index ≤ C) (href : position+negative.toNat ≤ C) :
    budget index position C negative ≤ 32*C+100 := by
  have hl:=RecoveryBoundedNativeLiteral.budget_bound index position C hi hp hz
  unfold budget RecoveryBoundedNativeLiteralStack.budget
  omega

theorem bounded_run (index position W C : ℕ) (negative : Bool) (out stack : List Bool)
    (hi : index ≤ W) (hp : position ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom machine (32*C+100) (entry index position C negative out stack)=some r ∧
      r.steps ≤ 32*C+100 ∧
      r.final.heads=heads (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) ∧
      r.final.tapes=data (index+1) (position+negative.toNat+1) C negative
        (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) 0 := by
  have capi:=PCPPNativeClauseCapacity.sum_capacity 0 index W C (by omega) hC
  have capp:=PCPPNativeClauseCapacity.sum_capacity 0 position W C (by omega) hC
  have capz:=PCPPNativeClauseCapacity.sum_capacity 0 0 W C (by omega) hC
  have small : 2*W+4 ≤ C := by nlinarith [Nat.zero_le (W*W)]
  have hn : negative.toNat ≤ 1 := by cases negative <;> decide
  obtain ⟨r,hr,rs,rh,rt⟩:=step_run index position C negative out stack capi capp capz
    (by omega) (by omega) (by omega)
  have hb:=budget_bound index position C negative capi capp capz (by omega) (by omega)
  have more:=runFrom_moreFuel machine _ (32*C+100-budget index position C negative) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rs.trans hb,rh,rt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStep
