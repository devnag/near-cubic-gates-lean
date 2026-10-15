import Proof.MachineModel.OrdinaryMatrixBatchRightPlane

/-! The entire original-request bucket producer has a quadratic envelope.
The all-gate term uses the genuine aggregate Gates*Buckets≤Capacity≤U,
while the reusable D-clears use Gates≤U. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightPlaneBounds
open MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def linear (r : Request) := 2*MatrixScoreReusableRanks.D r+16*H r+38+4*r.U*(4*H r+3)
def bucket (r : Request) := 4*r.U*(68*H r+8*r.M+63)+24*H r+4*r.M+38

theorem pass_cost (r : Request) : MatrixRightGatePass.budget r=2*r.Gates*linear r+2*r.Used*bucket r+16 := by
  unfold MatrixRightGatePass.budget MatrixRightGatePass.forwardBudget MatrixRightGateNativeLoop.budget
    MatrixRightGateBody.budget MatrixBucketGateLoad.budget MatrixBucketGateLoad.loadBudget
    MatrixBucketGatePrepare.budget MatrixRightNativeCall.budget MatrixBucketCallBounds.resetBudget
    Request.Used linear bucket
  ring

theorem pass_budget (r : Request) : MatrixRightGatePass.budget r≤10^9*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let q := r.d+r.p+1
  have hq : 1≤q := by dsimp [q]; omega
  have hqq : q≤q^2 := by nlinarith
  have hH : H r≤8*q := by
    have h := MatrixScoreRawRanksBounds.header_width r
    unfold H
    dsimp [q]
    omega
  have hM : r.M≤3*q := by rw [common_width]; dsimp [q]; omega
  have hD : MatrixScoreReusableRanks.D r≤200000000*r.U*q^2 := MatrixBatchAllRanksBounds.storage_bound r
  have hG : r.Gates≤r.U := (Nat.le_mul_self r.Gates).trans
    (r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U))
  have hUsed : r.Used≤r.U := (MatrixScoreBatch.capacity r).trans (WilliamsPaddedRequest.inner_le r.U)
  have hlinear : linear r≤400000400*(r.U+1)*q^2 := by
    have hbig := Nat.mul_le_mul_left (4*r.U) (show 4*H r+3≤35*q by omega)
    have hterm := Nat.mul_le_mul_left r.U hqq
    unfold linear
    nlinarith
  have hbucket : bucket r≤3100*(r.U+1)*q := by
    have hbig := Nat.mul_le_mul_left (4*r.U) (show 68*H r+8*r.M+63≤631*q by omega)
    unfold bucket
    nlinarith
  have hlin := Nat.mul_le_mul hG hlinear
  have hbat := Nat.mul_le_mul hUsed hbucket
  have hquad := Nat.mul_le_mul_left (6200*r.U*(r.U+1)) hqq
  have hone : 1≤(r.U+1)^2*q^2 := by
    have hpos : 0<(r.U+1)^2*q^2 := by positivity
    omega
  rw [pass_cost]
  change 2*r.Gates*linear r+2*r.Used*bucket r+16≤10^9*(r.U+1)^2*q^2
  nlinarith

theorem plane_budget (r : Request) : MatrixRightPlaneNative.budget r≤
    1000000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let q := r.d+r.p+1
  have hq : 1≤q := by dsimp [q]; omega
  have hqq : q≤q^2 := by nlinarith
  have hM : r.M≤3*q := by rw [common_width]; dsimp [q]; omega
  have hcap : r.Capacity≤r.U := WilliamsPaddedRequest.inner_le r.U
  have hu : r.Used≤r.U := (MatrixScoreBatch.capacity r).trans hcap
  have hn : r.Used*(2*r.U)≤2*(r.U+1)^2 := by nlinarith
  have hw : 64*r.M+47≤239*q := by omega
  have htrans := Nat.mul_le_mul hn hw
  have hqq' := Nat.mul_le_mul_left (478*(r.U+1)^2) hqq
  have hsize : r.Used*(r.U+r.U)+r.Capacity*r.U+r.Used+1≤4*(r.U+1)^2 := by nlinarith
  have hwidth : (r.M+r.M+2)^2≤64*q^2 := by nlinarith
  have hsort := Nat.mul_le_mul hsize hwidth
  have hp : 1≤(r.U+1)^2*q^2 := by
    have hpos : 0<(r.U+1)^2*q^2 := by positivity
    omega
  unfold MatrixRightPlaneNative.budget MatrixRightPlaneNative.forwardBudget MatrixRightPlaneNative.handoffBudget
    MatrixRightHandoff.budget
  rw [MatrixRightRecords.records_length]
  change 2*(1+1+((2*(r.Used*(2*r.U)*(64*r.M+47)+3)+2)+1+
    512*(r.Used*(r.U+r.U)+r.Capacity*r.U+r.Used+1)*(r.M+r.M+2)^2))+2≤1000000*(r.U+1)^2*q^2
  nlinarith

theorem return_budget (r : Request) : MatrixRightRankReturn.budget r≤
    200*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hrev := MatrixBatchRankReverseBounds.reverse_budget r
  have hsmall : MatrixRightRankReturn.budget r≤MatrixRankReverseEntry.budget (H r) r.U r.Gates := by
    unfold MatrixRightRankReturn.budget MatrixRankReverseEntry.budget
    omega
  have hq : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (200*(r.U+1)^2) hq
  exact hsmall.trans (hrev.trans hmul)

theorem bank_budget (r : Request) : MatrixRightBankEntry.budget r≤
    500000000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let q := r.d+r.p+1
  have hq : 1≤q := by dsimp [q]; omega
  have hqq : q≤q^2 := by nlinarith
  have hu : r.U≤(r.U+1)^2 := by nlinarith
  have hD := MatrixBatchAllRanksBounds.storage_bound r
  have hD' := Nat.mul_le_mul_right (q^2) hu
  have hM : r.M≤3*q := by rw [common_width]; dsimp [q]; omega
  have hqE := Nat.mul_le_mul (show 1≤(r.U+1)^2 by nlinarith) hqq
  have hp : 1≤(r.U+1)^2*q^2 := by
    have hpos : 0<(r.U+1)^2*q^2 := by positivity
    omega
  unfold MatrixRightBankEntry.budget
  change 2*MatrixScoreReusableRanks.D r+8*r.M+13≤500000000*(r.U+1)^2*q^2
  change MatrixScoreReusableRanks.D r≤200000000*r.U*q^2 at hD
  nlinarith

theorem padding_budget (r : Request) :
    8*(r.Capacity-r.Used)*r.U+10*(r.Capacity-r.Used)+28≤100*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hcap : r.Capacity-r.Used≤r.U := (Nat.sub_le _ _).trans (WilliamsPaddedRequest.inner_le r.U)
  have hpadmul := Nat.mul_le_mul_right r.U hcap
  have hq : 1≤(r.d+r.p+1)^2 := by
    have hpos : 0<(r.d+r.p+1)^2 := by positivity
    omega
  have hmul := Nat.mul_le_mul_left ((r.U+1)^2) hq
  nlinarith

theorem budget_le (r : Request) : MatrixBatchRightPlane.budget r≤
    4*10^11*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hleft := MatrixBatchLeftPlaneBounds.budget_le r
  have hpass := pass_budget r
  have hplane := plane_budget r
  have hreturn := return_budget r
  have hbank := bank_budget r
  have hpad := padding_budget r
  have hp : 1≤(r.U+1)^2*(r.d+r.p+1)^2 := by
    have hpos : 0<(r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold MatrixBatchRightPlane.budget MatrixBatchRightPadDriver.budget MatrixBatchRightPass.budget
    MatrixBatchRightBank.budget MatrixBatchRightReturn.budget
  nlinarith only [hleft,hpass,hplane,hreturn,hbank,hpad,hp]

end NearCubicWires.RepairOrdinary.MatrixBatchRightPlaneBounds
