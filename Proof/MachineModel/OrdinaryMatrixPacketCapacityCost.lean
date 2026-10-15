import Proof.MachineModel.OrdinaryMatrixPacketCapacityEntry

/-! The physical capacity producer runs in a constant multiple of the
capacity itself, with source-fixed degree/coefficient. No extra input
exponent is hidden in capacity production. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketCapacityCost
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem power_cost (E C q j : ℕ) (hq : 1≤q) (hj : j≤E) :
    DimensionPower.cost C q j≤2*C+2+j*(10*C*q^E+7) := by
  induction j with
  | zero => simp [DimensionPower.cost]
  | succ j ih =>
    have prev := ih (by omega)
    have h0 := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hq (show j≤E by omega))
    have h1 := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hq hj)
    simp only [pow_succ] at h1
    simp only [DimensionPower.cost,WilliamsUnaryProduct.budget]
    nlinarith only [prev,h0,h1]

theorem budget_bound (E C U d p : ℕ) (hE : 1≤E) (hC : 1≤C) :
    MatrixPacketCapacityEntry.budget E C U d p≤(20*E+148)*C*(U+1)^2*(d+p+1)^E := by
  let q := d+p+1
  let P := C*q^E
  let B := P*(U+1)^2
  have hq : 1≤q := by dsimp [q]; omega
  have hp : 1≤P := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hCP : C≤P := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  have hPB : P≤B := Nat.le_mul_of_pos_right _ (pow_pos (Nat.zero_lt_succ U) 2)
  have hB : 1≤B := hp.trans hPB
  have hPU : P*(U+1)≤B := Nat.mul_le_mul_left P (by nlinarith : U+1≤(U+1)^2)
  have hqP : q≤P := (Nat.le_self_pow (by omega : E≠0) q).trans (Nat.le_mul_of_pos_left _ hC)
  have hqB : q≤B := hqP.trans hPB
  have hUB : U≤B := (show U≤(U+1)^2 by nlinarith).trans (Nat.le_mul_of_pos_left _ hp)
  have hEP : E≤E*P := Nat.le_mul_of_pos_right _ hp
  have hpow := power_cost E C q E hq le_rfl
  have hpowP : DimensionPower.cost C q E≤(17*E+4)*P := by
    rw [Nat.mul_assoc 10 C (q^E)] at hpow
    change DimensionPower.cost C q E≤2*C+2+E*(10*P+7) at hpow
    nlinarith only [hpow,hCP,hp,hEP]
  have hpowB : DimensionPower.cost C q E≤(17*E+4)*B := hpowP.trans (Nat.mul_le_mul_left _ hPB)
  have hprod : WilliamsUnaryProduct.budget P (U+1)+1+WilliamsUnaryProduct.budget (P*(U+1)) (U+1)≤34*B := by
    have he : P*(U+1)*(U+1)=B := by dsimp [B]; ring
    unfold WilliamsUnaryProduct.budget
    nlinarith only [hPB,hPU,hB,he]
  have hdims : MatrixPacketCapacityDimensions.budget U d p≤77*B := by
    unfold MatrixPacketCapacityDimensions.budget
    dsimp [q] at hqB
    nlinarith only [hUB,hqB,hB]
  have heq : (20*E+148)*C*(U+1)^2*(d+p+1)^E=(20*E+148)*B := by
    dsimp [B,P,q]
    ring
  rw [heq]
  unfold MatrixPacketCapacityEntry.budget MatrixPacketCapacityPower.budget
  change MatrixPacketCapacityDimensions.budget U d p+1+
    (DimensionPower.cost C q E+1+WilliamsUnaryProduct.budget P (U+1)+1+
      WilliamsUnaryProduct.budget (P*(U+1)) (U+1))≤_
  nlinarith only [hdims,hpowB,hprod,hB]

end NearCubicWires.RepairOrdinary.MatrixPacketCapacityCost
