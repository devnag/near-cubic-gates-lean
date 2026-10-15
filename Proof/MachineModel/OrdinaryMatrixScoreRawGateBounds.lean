import Proof.MachineModel.OrdinaryMatrixScoreRawGate

/-! Quadratic-in-header-parameters accounting for the actual cold all-2U
record producer. Every setup, bank copy, arithmetic cycle and return remains
in the executed cost before domination. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRawGateBounds
open LocalBitMultitape SignedSortKey MatrixScoreBatch RepairRepresentation
open MatrixScoreLeftLoop (C)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `w` is the weight count (`r.width ≤ 2d`); the record cycles, the advance's `φ` step and the
halves reset are paid at `w`, the gate word's cut at `2w+2` fields. -/
def cost (d p bd bp U remaining w : ℕ) : ℕ :=
  let S := p+bd+2
  let W := S+1
  let M := d+3
  let cap := 4*(W+M)+18
  let headers := 4*((2*bd+1)+((2*bp+1)+(2*w+2)*(2*p+3)))+3+
    MatrixDimensionPrepare.budget bd d+1+MatrixDimensionPrepare.budget bp p
  let power := 8*d+40+MatrixUnaryTemplate.budget M U
  let dimensions := headers+4*d+16+power
  let widthEntry := dimensions+6*p+6*bd+51
  let constants := widthEntry+24*W+90
  let setup := constants+14*(W+M)+77
  let coldSetup := setup+1+MatrixScoreColdFields.budget d M cap
  let rawPrepare := coldSetup+1+1+1+MatrixScoreBankReady.budget d p
  let left := (MatrixScoreLeftCycle.budget w p S cap M+1+1)+1+
    (remaining*(MatrixScoreLeftNext.budget w p S cap M d+2)+U+3)
  let right := (MatrixScoreRightCycle.budget w p S cap M+1+1)+1+
    (remaining*(MatrixScoreRightNext.budget w p S cap M d+2)+U+3)
  let both := (left+1+MatrixScoreHalvesReset.budget w M d cap)+1+right
  2*(rawPrepare+1+(both+2))+2

theorem natWord_length (n : ℕ) : (natWord n).length=2*natBitLength n+1 := by
  rw [WilliamsInputHeader.natWord_eq]
  simp only [List.length_append,List.length_replicate,List.length_cons,binary_length]
  omega

theorem cost_eq (r : Request) (gate : Fin r.Gates) :
    MatrixScoreRawGate.budget r gate=cost r.d r.p (natBitLength r.d) (natBitLength r.p) r.U (r.U-1) r.width := by
  have hc := cutWord_length r (r.cuts.get gate) (List.get_mem _ _)
  have hm := common_width r
  unfold MatrixScoreRawGate.budget MatrixScoreRawGate.coreBudget MatrixScoreRawPrepare.budget
    MatrixScoreColdSetup.budget MatrixScoreSetup.budget MatrixScoreConstantsEntry.budget
    MatrixScoreWidthEntry.budget MatrixScoreDimensions.budget MatrixScoreHeaders.budget
    WilliamsInputHeader.budget MatrixScorePower.budget MatrixScoreGateStream.budget
    MatrixScoreBothHalves.budget MatrixScoreLeftEnumeration.budget MatrixScoreRightEnumeration.budget
  simp only [List.length_append,natWord_length,hc]
  unfold MatrixScoreSetup.width MatrixScoreSetup.capacity MatrixScoreCommonCapacity.capacity
    MatrixScoreCapacity.capacity MatrixScoreConstantsEntry.width C
  rw [hm]
  unfold Request.S cost
  rfl

theorem cost_mono (d p bd bp U remaining w H : ℕ)
    (hd : d≤H) (hp : p≤H) (hbd : bd≤H) (hbp : bp≤H) (hr : remaining≤U) (hw : w ≤ 2*H) :
    cost d p bd bp U remaining w≤cost H H H H U U (2*H) := by
  simp only [cost, MatrixDimensionPrepare.budget, MatrixUnaryTemplate.budget, MatrixScoreColdFields.budget,
    MatrixScoreBankReady.budget, MatrixScoreBankCut.budget, MatrixScoreHalvesReset.budget,
    MatrixScoreLeftCycle.budget, MatrixScoreRightCycle.budget, MatrixScoreLeftNext.budget,
    MatrixScoreRightNext.budget, MatrixScorePhiLayout.advanceBudget, MatrixScorePhi.budget, MatrixScoreLeftRecord.budget,
    MatrixScoreRightRecord.budget, MatrixScoreLeft.budget, MatrixScoreRight.budget,
    MatrixScoreLinear.budget, MatrixScoreFoldEntry.budget, MatrixScoreThresholdDriver.budget, MatrixScoreFinish.budget]
  gcongr

theorem uniform_cost (H U : ℕ) (hH : 1≤H) : cost H H H H U U (2*H)≤100000*(U+1)*H^2 := by
  simp only [cost, MatrixDimensionPrepare.budget, MatrixUnaryTemplate.budget, MatrixScoreColdFields.budget,
    MatrixScoreBankReady.budget, MatrixScoreBankCut.budget, MatrixScoreHalvesReset.budget,
    MatrixScoreLeftCycle.budget, MatrixScoreRightCycle.budget, MatrixScoreLeftNext.budget,
    MatrixScoreRightNext.budget, MatrixScorePhiLayout.advanceBudget, MatrixScorePhi.budget, MatrixScoreLeftRecord.budget,
    MatrixScoreRightRecord.budget, MatrixScoreLeft.budget, MatrixScoreRight.budget,
    MatrixScoreLinear.budget, MatrixScoreFoldEntry.budget, MatrixScoreThresholdDriver.budget, MatrixScoreFinish.budget]
  have hsq : H≤H^2 := by nlinarith
  have husq : U*H≤U*H^2 := Nat.mul_le_mul_left U hsq
  have hu : U≤U*H := by nlinarith
  nlinarith

theorem budget_le (r : Request) (gate : Fin r.Gates) :
    MatrixScoreRawGate.budget r gate≤100000*(r.U+1)*(r.d+r.p+1)^2 := by
  have hd : natBitLength r.d≤r.d+1 := by
    change Nat.log 2 r.d+1≤r.d+1
    exact Nat.add_le_add_right (Nat.log_le_self _ _) _
  have hp : natBitLength r.p≤r.p+1 := by
    change Nat.log 2 r.p+1≤r.p+1
    exact Nat.add_le_add_right (Nat.log_le_self _ _) _
  have hw := r.widthLe
  rw [cost_eq]
  exact (cost_mono _ _ _ _ _ _ _ (r.d+r.p+1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (uniform_cost _ _ (by omega))

end NearCubicWires.RepairOrdinary.MatrixScoreRawGateBounds
