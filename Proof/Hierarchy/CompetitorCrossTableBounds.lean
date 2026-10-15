import Proof.Hierarchy.CompetitorCrossTable

/-! Full executed cross-table bound, including the dimension printers,
capacity allocation, padding, zero-bank initialization and all plane pairs.
The raw number n appears linearly; all higher degree is in short widths. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossTableCold
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem preparation_bound (b w n p : ℕ) :
    CompetitorCrossTablePrepare.budget b w n p ≤ 2000000*(n+1)*(w+b+p+1)^2 := by
  unfold CompetitorCrossTablePrepare.budget CompetitorCrossScalarDrivers.budget
    CompetitorCrossCapacity.budget CompetitorCrossAffineDimensions.budget
    CompetitorCrossCapacity.slope CompetitorCrossCapacity.intercept CompetitorCrossAffineDimensions.value
    PCPSerializerCapacity.Power.budget DimensionPower.cost WilliamsUnaryProduct.budget Counter.budget
  rw [CompetitorCrossCapacity.capacity_formula]
  unfold CompetitorCrossCapacity.slope CompetitorCrossCapacity.intercept CompetitorCrossAffineDimensions.value
  simp only [DimensionPower.cost,WilliamsUnaryProduct.budget]
  ring_nf
  omega

theorem budget_bound (b w n p : ℕ) :
    budget b w n p ≤ 3000000*(n+1)*(w+b+p+1)^3 := by
  have hp := preparation_bound b w n p
  unfold budget CompetitorPlaneTableCold.budget CompetitorPlaneTableEntry.budget
    CompetitorPlaneTable.tableBudget CompetitorPlaneTable.pairFuel
  change CompetitorCrossTablePrepare.budget b w n p+1+
    (2*CompetitorPlanePacketPass.capacity w n+5+
      (p*(10*CompetitorPlanePacketPass.capacity w n+8*w+4*(n*w)+37+3)+3+4)) ≤ _
  rw [CompetitorCrossCapacity.capacity_formula]
  unfold CompetitorCrossCapacity.slope CompetitorCrossCapacity.intercept CompetitorCrossAffineDimensions.value
  ring_nf at hp ⊢
  omega

theorem request_bound (r : MatrixScoreBatch.Request) :
    budget (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p ≤
      375000000*(r.U+1)^2*(r.d+r.p+1)^3 := by
  have hb := budget_bound (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p
  have hd : natBitLength r.U=r.d+1 := by
    unfold MatrixScoreBatch.Request.U
    simp [natBitLength,Nat.log_pow]
  have hw : CompetitorPlaneWidth.width (natBitLength r.U) r.p+natBitLength r.U+r.p+1 ≤
      5*(r.d+r.p+1) := by
    rw [hd]
    unfold CompetitorPlaneWidth.width
    omega
  have hm := Nat.mul_le_mul (show r.U*r.U+1 ≤ (r.U+1)^2 by nlinarith) (Nat.pow_le_pow_left hw 3)
  have hscale := Nat.mul_le_mul_left 3000000 hm
  calc
    budget (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p
      ≤ 3000000*((r.U*r.U+1)*(CompetitorPlaneWidth.width (natBitLength r.U) r.p+natBitLength r.U+r.p+1)^3) := by simpa only [Nat.mul_assoc] using hb
    _ ≤ 3000000*((r.U+1)^2*(5*(r.d+r.p+1))^3) := hscale
    _ = 375000000*(r.U+1)^2*(r.d+r.p+1)^3 := by ring

end NearCubicWires.RepairOrdinary.CompetitorCrossTableCold
