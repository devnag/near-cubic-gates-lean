import Proof.CaseAnalysis.Capacity

/-! Paper C.12 budget for the actual cold capacity producer. The fixed
constants A,B may depend on the already selected recovery clock. This bound
is not used for the preprocessing exponent of the weak machine. -/
namespace NearCubicWires.RepairSource.CloseoutCapacity
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem power_budget (d : Nat) : Power.budget d ≤ 128*(d+3)*(2^d+1) := by
  unfold Power.budget MatrixScorePower.budget MatrixUnaryTemplate.budget
  ring_nf
  omega

theorem allocation_budget (A B : Nat) (bits : List Bool) :
    HierarchyAllocation.budget A B bits ≤ 64*(A+B+1)*(bits.length+1) := by
  unfold HierarchyAllocation.budget HierarchyAllocation.productCost HierarchyAllocation.offset
  nlinarith

def coefficient (A B : Nat) := 128*(A+B+3)*(2^B+1)+64*(A+B+1)+1

theorem budget_bound (A B : Nat) (bits : List Bool) :
    budget A B bits ≤ coefficient A B*(2^bits.length+1)^(A+1) := by
  let n:=bits.length
  let x:=2^n+1
  have hn : n+1 ≤ x := by
    have h : n < 2^n := Nat.lt_two_pow_self
    dsimp [x]
    omega
  have hx : 1 ≤ x := by dsimp [x];omega
  have hxp : x ≤ x^(A+1) := Nat.le_self_pow (by omega) _
  have h1 : 1 ≤ x^A := Nat.one_le_pow _ _ hx
  have h2 : 1 ≤ x^(A+1) := hx.trans hxp
  have hd : A*n+B+3 ≤ (A+B+3)*x := by
    have he : A*n+B+3 ≤ (A+B+3)*(n+1) := by nlinarith
    exact he.trans (Nat.mul_le_mul_left _ hn)
  have hu : 2^(A*n+B)+1 ≤ (2^B+1)*x^A := by
    have he : 2^(A*n+B)=2^B*(2^n)^A := by
      rw [pow_add,Nat.mul_comm A n,pow_mul]
      ring
    have hb : (2^n)^A ≤ x^A := Nat.pow_le_pow_left (by dsimp [x];omega) _
    rw [he]
    have hm:=Nat.mul_le_mul_left (2^B) hb
    nlinarith
  have hp : Power.budget (A*n+B) ≤ 128*(A+B+3)*(2^B+1)*x^(A+1) := by
    calc
      _ ≤ 128*(A*n+B+3)*(2^(A*n+B)+1) := power_budget _
      _ ≤ 128*((A+B+3)*x)*((2^B+1)*x^A) := Nat.mul_le_mul (Nat.mul_le_mul_left 128 hd) hu
      _ = _ := by rw [pow_succ];ring
  have ha : HierarchyAllocation.budget A B bits ≤ 64*(A+B+1)*x^(A+1) :=
    (allocation_budget A B bits).trans (Nat.mul_le_mul_left _ (hn.trans hxp))
  change budget A B bits ≤ coefficient A B*x^(A+1)
  unfold budget coefficient
  change HierarchyAllocation.budget A B bits+1+Power.budget (A*n+B) ≤ _
  nlinarith

end NearCubicWires.RepairSource.CloseoutCapacity
