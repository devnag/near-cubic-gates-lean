import Proof.MachineModel.OrdinarySourceSATLiftRequestEmit

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (code : List Bool) (C D n : ℕ) :=
  4096*(C+D+code.length+1)^2*(n+2)^(D+1)

theorem ledger_bound (code : List Bool) (C D n : ℕ) :
    prepareBudget C D n+emitBudget code C D n ≤ budget code C D n := by
  let A := C+D+code.length+1
  let X := (n+2)^(D+1)
  let Y := A^2*X
  have ha : 1 ≤ A := by dsimp [A]; omega
  have ha2 : A ≤ A^2 := by nlinarith
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hY : 1 ≤ Y := by
    exact Nat.mul_le_mul (Nat.one_le_pow _ _ ha) hX
  have hnX : n ≤ X := by
    have hp : (n+2)^1 ≤ (n+2)^(D+1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [pow_one] at hp
    omega
  have hXY : X ≤ Y := by
    have h := Nat.mul_le_mul_right X (Nat.one_le_pow 2 A ha)
    simpa only [Nat.one_mul] using h
  have hnY : n ≤ Y := hnX.trans hXY
  have hC : C ≤ A := by dsimp [A]; omega
  have hD : D ≤ A := by dsimp [A]; omega
  have hc : code.length ≤ A := by dsimp [A]; omega
  have hCY : C*X ≤ Y := Nat.mul_le_mul_right X (hC.trans ha2)
  have small (z : ℕ) (hz : z ≤ A) : z ≤ Y := by
    have h1 := Nat.mul_le_mul_left z hX
    have h2 := Nat.mul_le_mul_right X (hz.trans ha2)
    simpa only [Nat.mul_one] using h1.trans h2
  have hCp := small C hC
  have hDp := small D hD
  have hcp := small code.length hc
  have hCD : C*D*X ≤ Y := by
    have h := Nat.mul_le_mul_right X (Nat.mul_le_mul hC hD)
    simpa only [Y,pow_two] using h
  have hb : C*(n+1)^D ≤ Y := by
    have h1 : (n+1)^D ≤ (n+2)^D := Nat.pow_le_pow_left (by omega) D
    have h2 : (n+2)^D ≤ X := Nat.pow_le_pow_right (by omega) (by omega)
    exact (Nat.mul_le_mul_left C (h1.trans h2)).trans hCY
  have cost := DimensionPower.cost_bound D C (n+1) D le_rfl
  change DimensionPower.cost C (n+1) D ≤ 2*C+2+D*(6*C*X+7) at cost
  have cost' : DimensionPower.cost C (n+1) D ≤ 2*C+2+6*(C*D*X)+7*D := by
    calc
      _ ≤ 2*C+2+D*(6*C*X+7) := cost
      _ = _ := by ring
  have hh : (header code).length=8*code.length+4 := by
    simp only [header,Streaming.marks_length,frame_length]
    omega
  unfold prepareBudget emitBudget PCPSerializerCapacity.Power.budget budget
  rw [hh,Nat.mul_assoc]
  change 4*n+3+(2*n+9+DimensionPower.cost C (n+1) D+1)+
    (8*code.length+4+10*n+6*(C*(n+1)^D)+16) ≤ 4096*Y
  omega

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
