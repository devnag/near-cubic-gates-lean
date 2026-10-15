import Proof.CaseAnalysis.ScheduleBudget
import Proof.CaseAnalysis.CloseoutRecoveryBudget

/-! The already checked cold capacity producer suffices for every actual
schedule index. Its constants are fixed after the recovery clock. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem schedule_capacity (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (hD : 1 ≤ D) :
    ∃ A B : Nat, ∀ n,
      n+3 ≤ CloseoutCapacity.capacity A B n ∧
      2^n+3 ≤ CloseoutCapacity.capacity A B n ∧
      ∀ s, s ≤ n → Test.budget sources k D copies clock s n+1 ≤ CloseoutCapacity.capacity A B n := by
  obtain ⟨a,d,hbound⟩ := test_budget_uniform sources k D copies clock hD
  let e := natBitLength (a+4)+2*(d+1)+1
  refine ⟨e,e,?_⟩
  intro n
  let x : Nat := 2^n+1
  have hx : 1 ≤ x := Nat.succ_pos _
  have hp : x ≤ x^(d+1) := Nat.le_self_pow (by omega) _
  have hd : x^d ≤ x^(d+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hn : n < 2^n := Nat.lt_two_pow_self
  have hbig : (a+4)*x^(d+1) ≤ CloseoutCapacity.capacity e e n := by
    have he := Closeout.recovery_budget (a+4) (d+1) n
    have hm : max 1 n ≤ n+1 := by omega
    have hmul := Nat.mul_le_mul_left e hm
    have hlast : 2^(e*max 1 n) ≤ 2^(e*n+e) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    exact he.trans hlast
  have hsmall : 2^n+3 ≤ (a+4)*x^(d+1) := by
    change 2^n+1 ≤ x^(d+1) at hp
    have hpos : 1 ≤ x^(d+1) := hx.trans (Nat.le_self_pow (by omega) _)
    nlinarith
  refine ⟨(show n+3 ≤ 2^n+3 by omega).trans (hsmall.trans hbig),hsmall.trans hbig,?_⟩
  intro s hs
  exact (hbound n s hs).trans ((Nat.mul_le_mul_left a hd).trans
    ((Nat.mul_le_mul_right (x^(d+1)) (Nat.le_add_right a 4)).trans hbig))

end
end NearCubicWires.RepairSource.CloseoutSchedule
