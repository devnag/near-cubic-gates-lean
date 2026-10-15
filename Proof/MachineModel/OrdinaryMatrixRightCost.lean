import Proof.MachineModel.OrdinaryMatrixRightSort

/-! Charge the complete right sort/selection/padding consumer by the actual
number of records and padded output cells, polynomial only in key width. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightSort
open LocalBitMultitape SupplierPrinter CoordinateKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem plane_budget (M U Used Capacity : ℕ) :
    MatrixRightGrid.budget M U Used Capacity ≤
      16*(Used*(U+U)+Capacity*U+Used+1)*(M+M+2) := by
  let B := Used*(U+U)
  let D := B+Capacity*U+Used+1
  have hBD : B ≤ D := by dsimp [D]; omega
  have hUD : Used*U ≤ D := (Nat.mul_le_mul_left Used (Nat.le_add_right U U)).trans hBD
  have hUsed : Used ≤ D := by dsimp [D]; omega
  have hCap : Capacity*U ≤ D := by dsimp [D]; omega
  have hOne : 1 ≤ D := by dsimp [D]; omega
  have hPad : (Capacity-Used)*U ≤ D :=
    (Nat.mul_le_mul_right U (Nat.sub_le Capacity Used)).trans hCap
  have hFirst := Nat.mul_le_mul_right (4*M+3) hBD
  have hSecond : Used*(6*U+12) ≤ 18*D := by nlinarith only [hUD,hUsed]
  have h : MatrixRightGrid.budget M U Used Capacity ≤ D*(4*M+31) := by
    unfold MatrixRightGrid.budget
    change B*(4*M+3)+Used*(6*U+12)+2*((Capacity-Used)*U)+8 ≤ _
    nlinarith only [hFirst,hSecond,hPad,hOne]
  calc
    _ ≤ D*(4*M+31) := h
    _ ≤ 16*D*(M+M+2) := by nlinarith [Nat.zero_le (D*M)]
    _ = _ := rfl

theorem joined_budget {U Used Capacity : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (req : SortCarrier.Request) (hgrid : SortCarrier.sorted req=grid M M payload) :
    2*SortCarrier.budget req.records+3+MatrixRightGrid.budget M U Used Capacity ≤
      512*(Used*(U+U)+Capacity*U+Used+1)*(M+M+2)^2 := by
  have hc : req.records.length=Used*(U+U) := by
    have h := (SortCarrier.sorted_perm req).length_eq
    rw [hgrid] at h
    simpa [grid] using h.symm
  have hw := SortMatrix.width_le (Rows := Used) (Columns := 0) M M payload req hgrid
  have hs := SortCost.carrier_budget_le req
  have hm := Nat.mul_le_mul_left (128*(req.records.length+1))
    (Nat.pow_le_pow_left (by omega : SortPreparation.width req.records+1 ≤ M+M+2) 2)
  have hsort : SortCarrier.budget req.records ≤ 128*(Used*(U+U)+1)*(M+M+2)^2 := by
    rw [hc] at hs hm
    omega
  have hrow := plane_budget M U Used Capacity
  have hsq : M+M+2 ≤ (M+M+2)^2 := by nlinarith
  have hrow' := hrow.trans (Nat.mul_le_mul_left (16*(Used*(U+U)+Capacity*U+Used+1)) hsq)
  have hone : 1 ≤ (M+M+2)^2 := by nlinarith
  nlinarith only [hsort,hrow',hone,Nat.zero_le ((Used*(U+U))*(M+M+2)^2),
    Nat.zero_le ((Capacity*U+Used)*(M+M+2)^2)]

end NearCubicWires.RepairOrdinary.MatrixRightSort
