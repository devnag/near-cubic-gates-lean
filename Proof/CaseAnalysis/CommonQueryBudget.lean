import Proof.CaseAnalysis.CommonQueryClear
import Proof.CaseAnalysis.CloseoutRecoveryBudget

/-! The paid common reset covers both the old prefix padding and the new
recovery frame. Its constants use final input length and the selected clocks. -/
namespace NearCubicWires.RepairSource.CloseoutCommonQueryClear
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_bound (A B n : ℕ) :
    CloseoutCapacity.capacity A B n ≤ 2^B*(2^n+1)^A:=by
  change 2^(A*n+B) ≤ _
  rw [pow_add,Nat.mul_comm A n,pow_mul,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _)

theorem recovery_bound (C E A B n : ℕ) :
    C*(CloseoutCapacity.capacity A B n+1)^E ≤
      (C*(2^B+1)^E)*(2^n+1)^(A*E):=by
  have h:=capacity_bound A B n
  have hone:1 ≤ (2^n+1)^A:=Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le _))
  have hs:CloseoutCapacity.capacity A B n+1 ≤ (2^B+1)*(2^n+1)^A:=by nlinarith
  have hp:=Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs E)
  simpa only [Nat.mul_pow,←Nat.pow_mul,Nat.mul_assoc] using hp

theorem exists_capacity (prefixC prefixE recoveryC recoveryE Aw Bw : ℕ) :
    ∃ A B : ℕ,∀ n,
      max (prefixC*(2^n+1)^prefixE)
        (recoveryC*(CloseoutCapacity.capacity Aw Bw n+1)^recoveryE) ≤
          CloseoutCapacity.capacity A B n:=by
  let C:=prefixC+recoveryC*(2^Bw+1)^recoveryE
  let E:=prefixE+Aw*recoveryE
  let a:=natBitLength C+2*E+1
  refine ⟨a,a,fun n=>?_⟩
  have hb:=recovery_bound recoveryC recoveryE Aw Bw n
  have h1:(2^n+1)^prefixE ≤ (2^n+1)^E:=Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp [E];omega)
  have h2:(2^n+1)^(Aw*recoveryE) ≤ (2^n+1)^E:=Nat.pow_le_pow_right (Nat.succ_pos _) (by dsimp [E];omega)
  have hsum:max (prefixC*(2^n+1)^prefixE)
      (recoveryC*(CloseoutCapacity.capacity Aw Bw n+1)^recoveryE) ≤ C*(2^n+1)^E:=by
    apply max_le
    · exact (Nat.mul_le_mul_left prefixC h1).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    · exact hb.trans ((Nat.mul_le_mul_left _ h2).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))
  apply hsum.trans ((Closeout.recovery_budget C E n).trans ?_)
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  change a*max 1 n ≤ a*n+a
  have hm:max 1 n ≤ n+1:=by omega
  nlinarith

theorem budget_bound (A B : ℕ) (bits : List Bool) :
    budget A B bits ≤ (CloseoutCapacity.coefficient A B+2*2^B+5)*(2^bits.length+1)^(A+1):=by
  have hp:=CloseoutCapacity.budget_bound A B bits
  have hc:=capacity_bound A B bits.length
  have hx:1 ≤ (2^bits.length+1)^(A+1):=Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le _))
  have hm:(2^bits.length+1)^A ≤ (2^bits.length+1)^(A+1):=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)
  have hc':CloseoutCapacity.capacity A B bits.length ≤ 2^B*(2^bits.length+1)^(A+1):=
    hc.trans (Nat.mul_le_mul_left _ hm)
  unfold budget
  nlinarith

end NearCubicWires.RepairSource.CloseoutCommonQueryClear
