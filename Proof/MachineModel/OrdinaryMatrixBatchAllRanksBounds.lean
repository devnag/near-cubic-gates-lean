import Proof.MachineModel.OrdinaryMatrixBatchAllRanks

namespace NearCubicWires.RepairOrdinary.MatrixBatchAllRanksBounds
open LocalBitMultitape SignedSortKey MatrixScoreBatch RepairRepresentation
open MatrixScoreLeftLoop (C)
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cost (d p bd bp bg U G T storage w bw : ℕ) :=
  let W := p+bd+3
  let M := d+3
  let cap := 4*(W+M)+18
  let suffix := 2*bg+1+((2*bw+1)+(d*(2*w+1)+G*((2*w+2)*(2*p+3))))
  let headers := 4*((2*bd+1)+((2*bp+1)+suffix))+3+
    MatrixDimensionPrepare.budget bd d+1+MatrixDimensionPrepare.budget bp p
  let power := 8*d+40+MatrixUnaryTemplate.budget M U
  let dimensions := headers+4*d+16+power
  let widthEntry := dimensions+6*p+6*bd+51
  let constants := widthEntry+24*W+90
  let setup := constants+14*(W+M)+77+1+MatrixDimensionPrepare.budget bg G
  let native := setup+1+MatrixScoreColdFields.budget d M cap
  let workspace := native+1+(1+1+T)
  let widthSetup := MatrixDimensionPrepare.budget bw w+1+(2*d+2*(d*(2*w+1))+5)+1+
    (4*w+14)+1+(4*w+4)+1+(4*w+4)+1+1
  workspace+1+widthSetup+1+(8*M+10)+1+(G*(16*storage+43)+3)

theorem cuts_length (r : Request) :
    (r.cuts.flatMap (cutWord r.p)).length=r.Gates*((2*r.width+2)*(2*r.p+3)) := by
  have h := word_length r
  change (header r++r.cuts.flatMap (cutWord r.p)).length=_ at h
  rw [List.length_append] at h
  omega

theorem cost_eq (r : Request) : MatrixBatchAllRanks.budget r=
    cost r.d r.p (natBitLength r.d) (natBitLength r.p) (natBitLength r.Gates) r.U r.Gates
      (MatrixBatchCapacity.budget (C r) r.U) (D r) r.width (natBitLength r.width) := by
  unfold MatrixBatchAllRanks.budget MatrixBatchGateColdEntry.budget MatrixBatchWorkspace.budget
    MatrixBatchNativeFields.budget MatrixBatchSetup.budget MatrixScoreSetup.budget
    MatrixScoreConstantsEntry.budget MatrixScoreWidthEntry.budget MatrixScoreDimensions.budget
    MatrixScoreHeaders.budget WilliamsInputHeader.budget MatrixScorePower.budget
    MatrixBatchGateColdCopy.budget MatrixBatchGateNativeLoop.budget MatrixBatchGateStore.budget
    MatrixBatchWidthSetup.budget MatrixBatchWidthSetup.parseBudget MatrixBatchColumnsCopy.budget MatrixBatchSetup.tail
  simp only [List.length_append,MatrixScoreRawGateBounds.natWord_length,cuts_length,MatrixScorePhi.columnsWord_length,
    cols_length]
  unfold MatrixScoreSetup.width MatrixScoreConstantsEntry.width C
  rw [common_width]
  unfold Request.S Request.U cost
  ring

theorem gate_width (r : Request) : natBitLength r.Gates≤r.d+1 := by
  have hs : r.Gates*r.Gates≤r.U := r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U)
  have hg : r.Gates≤r.U := by nlinarith
  have hl := Nat.log_mono_right (b := 2) hg
  change Nat.log 2 r.Gates≤Nat.log 2 (2^r.d) at hl
  rw [Nat.log_pow (by decide)] at hl
  exact Nat.add_le_add_right hl 1

theorem storage_bound (r : Request) : D r≤200000000*r.U*(r.d+r.p+1)^2 := by
  have hd : natBitLength r.d≤r.d+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hc : C r+1≤55*(r.d+r.p+1) := by
    unfold C Request.S
    rw [common_width]
    omega
  have hs := Nat.mul_le_mul_left r.U (Nat.pow_le_pow_left hc 2)
  unfold D MatrixBatchCapacity.capacity
  nlinarith

theorem cost_mono (d p bd bp bg U G T storage w bw H T' storage' : ℕ)
    (hd : d≤H) (hp : p≤H) (hbd : bd≤H) (hbp : bp≤H) (hbg : bg≤H) (hw : w≤2*H) (hbw : bw≤2*H)
    (ht : T≤T') (hs : storage≤ storage') :
    cost d p bd bp bg U G T storage w bw≤cost H H H H H U G T' storage' (2*H) (2*H) := by
  simp only [cost,MatrixDimensionPrepare.budget,MatrixUnaryTemplate.budget,MatrixScoreColdFields.budget]
  gcongr

theorem uniform_cost (H U G : ℕ) (hH : 1≤H) :
    cost H H H H H U G (20*(200000000*U*H^2)) (200000000*U*H^2) (2*H) (2*H)≤
      10000000000*(G+1)*(U+1)*H^2 := by
  have hs : H≤H^2 := by nlinarith
  have hs1 : 1≤H^2 := by nlinarith
  have hu := Nat.mul_le_mul_left U hs
  have hg := Nat.mul_le_mul_left G hs
  have hu1 := Nat.mul_le_mul_left U hs1
  have hg1 := Nat.mul_le_mul_left G hs1
  simp only [cost,MatrixDimensionPrepare.budget,MatrixUnaryTemplate.budget,MatrixScoreColdFields.budget]
  nlinarith

def envelope (r : Request) := 10000000000*(r.Gates+1)*(r.U+1)*(r.d+r.p+1)^2
theorem budget_le (r : Request) : MatrixBatchAllRanks.budget r≤envelope r := by
  have hd : natBitLength r.d≤r.d+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hp : natBitLength r.p≤r.p+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hg := gate_width r
  have hs := storage_bound r
  have ht := (MatrixBatchCapacity.budget_bound (C r) r.U (Nat.one_le_two_pow)).trans
    (Nat.mul_le_mul_left 20 hs)
  have hwl := r.widthLe
  have hbw : natBitLength r.width≤r.d+1 := natBitLength_width_le_succ r
  rw [cost_eq]
  exact (cost_mono _ _ _ _ _ _ _ _ _ _ _ (r.d+r.p+1) _ _ (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) ht hs).trans (uniform_cost _ _ _ (by omega))

end NearCubicWires.RepairOrdinary.MatrixBatchAllRanksBounds
