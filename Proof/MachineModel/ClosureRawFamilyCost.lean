import Proof.MachineModel.ClosureRawRelabelFamily
import Proof.MachineModel.P1ClosureCompactColdCost

/-! Charge the actual whole raw-index family additively before the compact
native writer. The reset is paid; no residual-table factor occurs here. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.RawFamilyCost

theorem family_bound (N Y S X : Nat) (hN : N≤X) (hY : Y≤X) (hS : S≤X) :
    RawRelabelFamily.budget N Y S≤128*(X+1)^4 := by
  have poly : RawRelabelFamily.budget N Y S≤4*X^4+6*X^3+20*X^2+38*X+3 := by
    calc
      _=4*N*Y^2*S+6*N*Y^2+6*N*Y+12*S*Y+2*Y^2+38*Y+3 := by
        unfold RawRelabelFamily.budget RawRelabelFamily.bodyBudget RawRelabelUniform.budget
          RawRelabelOffset.budget RawRelabelOffset.rawBudget RawRelabelUniform.capacity
        ring
      _≤4*X*X^2*X+6*X*X^2+6*X*X+12*X*X+2*X^2+38*X+3 := by gcongr
      _=4*X^4+6*X^3+20*X^2+38*X+3 := by ring
  have powers (i : Nat) (hi : i≤4) : X^i≤(X+1)^4 :=
    (Nat.pow_le_pow_left (by omega) i).trans (Nat.pow_le_pow_right (by omega) hi)
  have h1 := powers 1 (by decide)
  have h2 := powers 2 (by decide)
  have h3 := powers 3 (by decide)
  have h4 := powers 4 (by decide)
  have hone : 1≤(X+1)^4 := Nat.one_le_pow _ _ (by omega)
  simp only [pow_one] at h1
  omega

theorem prepared_bound (N Y S X w Q cold : Nat)
    (hN : N≤X) (hY : Y≤X) (hS : S≤X)
    (hcold : cold≤2^119*(X+1)^22*2^(w*(Q+1))) :
    (2*RawRelabelFamily.budget N Y S+2)+1+cold≤2^120*(X+1)^22*2^(w*(Q+1)) := by
  have hf := family_bound N Y S X hN hY hS
  have hp : (X+1)^4≤(X+1)^22 := Nat.pow_le_pow_right (by omega) (by decide)
  have he : 1≤2^(w*(Q+1)) := Nat.one_le_two_pow
  have hz : 1≤(X+1)^22 := Nat.one_le_pow _ _ (by omega)
  have hze : (X+1)^22≤(X+1)^22*2^(w*(Q+1)) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

end NearCubicWires.P1Closure.RawFamilyCost
