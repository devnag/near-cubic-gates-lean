import Proof.PCP.PCPSerializerCapacityReady

/-! Uniform polynomial ledger for the actual measured-capacity producer. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerCapacity
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient (D C : ℕ) := (48+2*C+7*D+6*D*C)*2^(D+1)

theorem budget_bound (D C B : ℕ) : budget D C B ≤ coefficient D C*(B+1)^(D+1) := by
  have hc := DimensionPower.cost_bound D C (B+1) D le_rfl
  change DimensionPower.cost C (B+1) D ≤ 2*C+2+D*(6*C*(B+2)^(D+1)+7) at hc
  let P := (B+2)^(D+1)
  have hP : 1 ≤ P := by dsimp [P]; exact Nat.one_le_pow _ _ (by omega)
  have hB : B ≤ P := by
    have h := Nat.pow_le_pow_right (by omega : 0<B+2) (by omega : 1 ≤ D+1)
    simpa only [pow_one] using (show B ≤ (B+2)^1 from by simp).trans h
  have hscale : 18*B+30+2*C+7*D ≤ (48+2*C+7*D)*P := by
    have h1 := Nat.mul_le_mul_left 18 hB
    have h2 := Nat.mul_le_mul_left (30+2*C+7*D) hP
    nlinarith
  have hsmall : budget D C B ≤ (48+2*C+7*D+6*D*C)*P := by
    dsimp only [budget,Power.budget]
    dsimp only [P] at hscale ⊢
    nlinarith
  have hp : (B+2)^(D+1) ≤ (2*(B+1))^(D+1) :=
    Nat.pow_le_pow_left (by omega) _
  rw [Nat.mul_pow] at hp
  have hmul := Nat.mul_le_mul_left (48+2*C+7*D+6*D*C) hp
  dsimp only [coefficient]
  rw [Nat.mul_assoc]
  exact hsmall.trans hmul

end NearCubicWires.RepairOrdinary.PCPSerializerCapacity
