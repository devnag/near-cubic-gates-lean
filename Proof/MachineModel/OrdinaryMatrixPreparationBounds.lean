import Proof.MachineModel.OrdinaryMatrixWilliamsProduct

/-! The complete explicit preprocessing/source call has a uniform quadratic
assignment-table envelope. This is the physical clear capacity supplier for
repeating the cold call, with the source logarithmic exponent retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsProductBounds
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem preparation_eq (r : Request) : MatrixWilliamsInput.budget r=
    MatrixBatchCoefficientPlanes.budget r+MatrixUnaryTemplate.budget r.M r.U+
    MatrixSignedMaskPass.budget r+18*r.d+20*r.U*r.Capacity+10*r.U+108 := by
  unfold MatrixWilliamsInput.budget MatrixWilliamsDimensions.budget MatrixWilliamsHeaderEntry.budget
    MatrixFirstSignedPlane.budget MatrixSignedEntry.budget MatrixSignedUEntry.budget
  ring

theorem unary_bound (r : Request) : MatrixUnaryTemplate.budget r.M r.U≤100*(r.U+1)*(r.d+r.p+1) := by
  unfold MatrixUnaryTemplate.budget
  rw [MatrixScoreBatch.common_width]
  nlinarith

theorem preparation_bound (r : Request) : MatrixWilliamsInput.budget r≤10^12*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let q := r.d+r.p+1
  let u := r.U+1
  let B := u^2*q^2
  have hq : 1≤q := by dsimp [q]; omega
  have hu : 1≤u := by dsimp [u]; omega
  have hqq : q≤q^2 := by nlinarith
  have huu : u≤u^2 := by nlinarith
  have hq2 : 1≤q^2 := by nlinarith
  have hu2 : 1≤u^2 := by nlinarith
  have hB1 : 1≤B := by dsimp [B]; nlinarith
  have hBu : u^2≤B := by dsimp [B]; nlinarith
  have hBq : q^2≤B := by dsimp [B]; nlinarith
  have huq : u*q≤B := by
    have h := Nat.mul_le_mul huu hqq
    exact h
  have hunit : MatrixUnaryTemplate.budget r.M r.U≤100*B :=
    (unary_bound r).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 100 huq)
  have hpq : r.p+1≤q^2 := by dsimp [q] at hqq ⊢; omega
  have hmask : MatrixSignedMaskPass.budget r≤128*B :=
    (MatrixSignedMaskBounds.budget_le r).trans (by
      dsimp only [B,u,MatrixSignedMaskBounds.capacity]
      calc
        _ = 128*((r.U+1)^2*(r.p+1)) := Nat.mul_assoc _ _ _
        _ ≤ _ := Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left ((r.U+1)^2) hpq))
  have hcap : r.Capacity≤r.U := WilliamsPaddedRequest.inner_le r.U
  have hmul : r.U*r.Capacity≤B := by
    have hm : r.U*r.Capacity≤u^2 := by dsimp [u]; nlinarith
    exact hm.trans hBu
  have hd : r.d≤B := by
    have hdq : r.d≤q := by dsimp [q]; omega
    exact hdq.trans (hqq.trans hBq)
  have hU : r.U≤B := (Nat.le_add_right r.U 1).trans (huu.trans hBu)
  have htail : 18*r.d+20*r.U*r.Capacity+10*r.U+108≤156*B := by nlinarith only [hd,hmul,hU,hB1]
  have hbase : MatrixBatchCoefficientPlanes.budget r≤5*10^11*B := by
    simpa only [B,u,q,Nat.mul_assoc] using MatrixCoefficientBounds.budget_le r
  rw [preparation_eq]
  calc
    _ = (MatrixBatchCoefficientPlanes.budget r+MatrixUnaryTemplate.budget r.M r.U+MatrixSignedMaskPass.budget r)+
        (18*r.d+20*r.U*r.Capacity+10*r.U+108) := by ring
    _ ≤ (5*10^11*B+100*B+128*B)+156*B :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hbase hunit) hmask) htail
    _ = (5*10^11+384)*B := by ring
    _ ≤ 10^12*B := Nat.mul_le_mul_right B (by norm_num)
    _ = _ := by dsimp [B,u,q]; ring

theorem log_bound (r : Request) : logScale r.U+1≤3*(r.d+r.p+1) := by
  have h : logScale r.U≤r.d+2 := by
    unfold logScale
    apply Nat.clog_le_of_le_pow
    change 2^r.d+2≤2^(r.d+2)
    have hp : 1≤2^r.d := Nat.one_le_two_pow
    simp only [pow_add,pow_two]
    nlinarith
  omega

end NearCubicWires.RepairOrdinary.MatrixWilliamsProductBounds
