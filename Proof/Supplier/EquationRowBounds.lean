import Proof.Supplier.EquationRowRaw

/-! The complete raw row producer has a fixed cubic parameter envelope,
plus its single linear scan of the actual original word. -/
namespace NearCubicWires.RepairOrdinary.EquationRowRaw
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mass (r : EquationRow.Input) := r.d+r.p+r.cuts.length+1

theorem cost_eq (r : EquationRow.Input) : budget r=
    4*(source r).length+
      MatrixDimensionPrepare.budget (natBitLength r.d) r.d+
      MatrixDimensionPrepare.budget (natBitLength r.p) r.p+
      MatrixDimensionPrepare.budget (natBitLength r.cuts.length) r.cuts.length+
      EquationCountReady.budget r.d r.p r.cuts.length+
      EquationHeaders.budget (EquationHeaderCold.values r.d r.p r.cuts.length)+
      2*EquationRowCuts.rowCapacity r+
      EquationRowCuts.budget r.cuts.length (EquationRowCuts.rowCapacity r)+17+
      (1+EquationRowPhiHeader.eraseBudget r.d r.p)+(1+EquationHeaderAppend.budget r.d)+
      (1+EquationIdentityColumns.budget r.d) := by
  have he : natWord r.d++(natWord r.p++(natWord r.cuts.length++
      (r.odd::EquationRowCuts.stream r.p r.cuts)))=source r := by
    simp only [source,EquationHeaderRead.word,EquationHeaderRead.header,List.append_assoc]
  unfold budget EquationRowPrepare.budget EquationHeaderCold.budget EquationCountCold.budget
    EquationHeaderBoot.budget EquationHeaderRead.budget MatrixScoreHeaders.budget WilliamsInputHeader.budget
  rw [he]
  unfold EquationRowPrepare.capacity EquationRowCuts.rowCapacity
  ring

theorem dimension_bound (n w H : ℕ) (hn : n ≤ H) (hw : w ≤ H) (hH : 1 ≤ H) :
    MatrixDimensionPrepare.budget w n ≤ 64*H^2 := by
  have hh := Nat.le_mul_self H
  calc
    MatrixDimensionPrepare.budget w n ≤ H*(8*H+10)+14*H+H+25 := by
      unfold MatrixDimensionPrepare.budget
      gcongr
    _ ≤ 64*H^2 := by nlinarith

theorem append_bound (n H : ℕ) (hn : n ≤ 2*H) (hH : 1 ≤ H) :
    EquationHeaderAppend.budget n ≤ 400*H^2 := by
  have hw : natBitLength n ≤ n+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hh := Nat.le_mul_self H
  calc
    EquationHeaderAppend.budget n ≤ 16*(2*H)^2+72*(2*H)+12*(2*H+1)+58 := by
      unfold EquationHeaderAppend.budget
      gcongr
      omega
    _ ≤ 400*H^2 := by nlinarith

theorem budget_polynomial (r : EquationRow.Input) :
    budget r ≤ 100000*(mass r)^3+4*(source r).length := by
  let H := mass r
  have hH : 1 ≤ H := by dsimp [H,mass]; omega
  have hd : r.d+1 ≤ H := by dsimp [H,mass]; omega
  have hp : r.p+1 ≤ H := by dsimp [H,mass]; omega
  have hg : r.cuts.length+1 ≤ H := by dsimp [H,mass]; omega
  have bd : natBitLength r.d ≤ H := (Nat.add_le_add_right (Nat.log_le_self _ _) 1).trans hd
  have bp : natBitLength r.p ≤ H := (Nat.add_le_add_right (Nat.log_le_self _ _) 1).trans hp
  have bg : natBitLength r.cuts.length ≤ H := (Nat.add_le_add_right (Nat.log_le_self _ _) 1).trans hg
  have dd := dimension_bound r.d (natBitLength r.d) H (by omega) bd hH
  have dp := dimension_bound r.p (natBitLength r.p) H (by omega) bp hH
  have dg := dimension_bound r.cuts.length (natBitLength r.cuts.length) H (by omega) bg hH
  have count : EquationCountReady.budget r.d r.p r.cuts.length ≤ 8192*H^2 :=
    EquationCountReady.budget_polynomial r.d r.p r.cuts.length
  have ad := append_bound r.d H (by omega) hH
  have ap := append_bound (r.p+1) H (by omega) hH
  have ag := append_bound (2*r.cuts.length) H (by omega) hH
  have hsquare : 1 ≤ H^2 := by nlinarith
  have headers : EquationHeaders.budget (EquationHeaderCold.values r.d r.p r.cuts.length) ≤ 1202*H^2 := by
    change EquationHeaderAppend.budget r.d+1+EquationHeaderAppend.budget (r.p+1)+1+
      EquationHeaderAppend.budget (2*r.cuts.length) ≤ _
    omega
  have cap : EquationRowCuts.rowCapacity r ≤ 256*H^2 := by
    calc
      EquationRowCuts.rowCapacity r = 128*(2*r.d+1)*(r.p+1) := rfl
      _ ≤ 128*(2*H)*H := by gcongr; omega
      _ = 256*H^2 := by ring
  have h23 : H^2 ≤ H^3 := by
    calc
      H^2 = 1*H^2 := by ring
      _ ≤ H*H^2 := Nat.mul_le_mul_right _ hH
      _ = H^3 := by ring
  have h13 : H ≤ H^3 := (by simpa only [pow_two] using Nat.le_mul_self H : H ≤ H^2).trans h23
  have eb : EquationRowPhiHeader.eraseBudget r.d r.p ≤ 8*H^2 := by
    unfold EquationRowPhiHeader.eraseBudget EquationRowPhiHeader.driverLength
    nlinarith
  have wb : EquationIdentityColumns.budget r.d ≤ 64*H^2 := by
    unfold EquationIdentityColumns.budget
    nlinarith
  have loop : EquationRowCuts.budget r.cuts.length (EquationRowCuts.rowCapacity r) ≤ 4102*H^3 := by
    calc
      EquationRowCuts.budget r.cuts.length (EquationRowCuts.rowCapacity r) ≤ H*(16*(256*H^2)+3)+3 := by
        unfold EquationRowCuts.budget
        gcongr; omega
      _ = 4096*H^3+3*H+3 := by ring
      _ ≤ 4102*H^3 := by omega
  rw [cost_eq]
  change _ ≤ 100000*H^3+4*(source r).length
  omega

end NearCubicWires.RepairOrdinary.EquationRowRaw
