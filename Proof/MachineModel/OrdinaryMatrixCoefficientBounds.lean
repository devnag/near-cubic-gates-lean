import Proof.MachineModel.OrdinaryMatrixBatchCoefficientPlanes

/-! The coefficient bank is prepared once in linear gate count and
polynomial scalar width. Its enclosing matrix parent retains the required
quadratic assignment-table bound, including every physical header/return.
The weight count satisfies `width ≤ 2d` (`Request.widthLe`), so the header's
columns (`d·(2·width+1)` cells) and the weight-count parse stay quadratic. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientBounds
open LocalBitMultitape MatrixScoreBatch SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The cold coefficient pass's cost: the three-header parse over the whole word (its length now includes
the weight count and the `d` framed columns, and each cut carries `2·width+2` fields), the three zeroing
sweeps, the weight-count parse, the columns pass, then the gate pass with `width` weights per side. -/
def cost (d p w bd bp bg bw G : ℕ) :=
  2*(4*(2*bd+1+(2*bp+1)+(2*bg+1)+((2*bw+1)+d*(2*w+1))+G*((2*w+2)*(2*p+3)))+3+
    MatrixDimensionPrepare.budget bd d+1+MatrixDimensionPrepare.budget bp p+
    1+MatrixDimensionPrepare.budget bg G+
    1+(2*bd+4)+1+(2*bp+4)+1+(2*bg+4)+1+MatrixDimensionPrepare.budget bw w+1+1+1+(2*d+2*(d*(2*w+1))+5)+
    1+G*(2*w*(2*p+6)+4*p+15+3)+3)+2

theorem cost_eq (r : Request) : MatrixCoefficientCold.budget r=
    cost r.d r.p r.width (natBitLength r.d) (natBitLength r.p) (natBitLength r.Gates) (natBitLength r.width)
      r.Gates := by
  unfold MatrixCoefficientCold.budget MatrixCoefficientCold.forwardBudget MatrixCoefficientHeaders.budget
    MatrixScoreHeaders.budget WilliamsInputHeader.budget MatrixCoefficientNative.budget MatrixCoefficientGate.budget
    MatrixBatchColumnsCopy.budget
  have hword : natWord r.d++(natWord r.p++(natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++
      r.cuts.flatMap (cutWord r.p)))=word r := by
    simp only [word,header,List.append_assoc]
  rw [hword,word_length]
  simp only [header,List.length_append,MatrixScoreRawGateBounds.natWord_length,MatrixScorePhi.columnsWord_length,
    cols_length]
  unfold cost
  ring

theorem cost_mono (d p w bd bp bg bw G H : ℕ) (hd : d≤H) (hp : p≤H) (hw : w≤2*H)
    (hbd : bd≤H) (hbp : bp≤H) (hbg : bg≤H) (hbw : bw≤H) :
    cost d p w bd bp bg bw G≤cost H H (2*H) H H H H G := by
  simp only [cost,MatrixDimensionPrepare.budget]
  gcongr

theorem uniform_cost (H G : ℕ) (hH : 1≤H) : cost H H (2*H) H H H H G≤1000*(G+1)*H^2 := by
  have h1 : 1≤H^2 := by nlinarith
  have h2 : H≤H^2 := by nlinarith
  have hg1 := Nat.mul_le_mul_left G h1
  have hg2 := Nat.mul_le_mul_left G h2
  unfold cost MatrixDimensionPrepare.budget
  nlinarith

theorem coefficient_budget (r : Request) : MatrixCoefficientCold.budget r≤
    1000*(r.U+1)*(r.d+r.p+1)^2 := by
  have hd : natBitLength r.d≤r.d+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hp : natBitLength r.p≤r.p+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hg := MatrixBatchAllRanksBounds.gate_width r
  have hbw := natBitLength_width_le_succ r
  have hw := r.widthLe
  have hG : r.Gates≤r.U := (Nat.le_mul_self r.Gates).trans
    (r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U))
  rw [cost_eq]
  exact ((cost_mono _ _ _ _ _ _ _ _ (r.d+r.p+1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)).trans (uniform_cost _ _ (by omega))).trans (by gcongr)

theorem budget_le (r : Request) : MatrixBatchCoefficientPlanes.budget r≤
    5*10^11*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hc := coefficient_budget r
  have hm := MatrixBatchRightPlaneBounds.budget_le r
  have hu : r.U+1≤(r.U+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_right ((r.d+r.p+1)^2) hu
  have hq : 1≤(r.d+r.p+1)^2 := by
    have hpos : 0<(r.d+r.p+1)^2 := by positivity
    omega
  have hp := Nat.mul_le_mul_left ((r.U+1)^2) hq
  unfold MatrixBatchCoefficientPlanes.budget
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixCoefficientBounds
