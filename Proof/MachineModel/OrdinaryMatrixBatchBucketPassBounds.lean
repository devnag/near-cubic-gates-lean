import Proof.MachineModel.OrdinaryMatrixBatchBucketPass

/-! The entire original-request bucket producer has a quadratic envelope.
The all-gate term uses the genuine aggregate Gates*Buckets≤Capacity≤U,
while the reusable D-clears use Gates≤U. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketPassBounds
open MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def linear (r : Request) := 2*MatrixScoreReusableRanks.D r+8*H r+30+4*r.U*(4*H r+3)
def bucket (r : Request) := 4*r.U*(68*H r+8*r.M+63)+12*H r+4*r.M+24

theorem pass_cost (r : Request) : MatrixBucketGatePass.budget r=2*r.Gates*linear r+2*r.Used*bucket r+16 := by
  unfold MatrixBucketGatePass.budget MatrixBucketGatePass.forwardBudget MatrixBucketGateNativeLoop.budget
    MatrixBucketGateBody.budget MatrixBucketGateLoad.budget MatrixBucketGateLoad.loadBudget
    MatrixBucketGatePrepare.budget MatrixBucketNativeReturn.budget MatrixBucketNativeCall.budget
    MatrixBucketCallBounds.resetBudget Request.Used linear bucket
  ring

theorem pass_budget (r : Request) : MatrixBucketGatePass.budget r≤10^9*(r.U+1)^2*(r.d+r.p+1)^2 := by
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
  have hlinear : linear r≤400000200*(r.U+1)*q^2 := by
    have hbig := Nat.mul_le_mul_left (4*r.U) (show 4*H r+3≤35*q by omega)
    have hterm := Nat.mul_le_mul_left r.U hqq
    unfold linear
    nlinarith
  have hbucket : bucket r≤3000*(r.U+1)*q := by
    have hbig := Nat.mul_le_mul_left (4*r.U) (show 68*H r+8*r.M+63≤631*q by omega)
    unfold bucket
    nlinarith
  have hlin := Nat.mul_le_mul hG hlinear
  have hbat := Nat.mul_le_mul hUsed hbucket
  have hquad := Nat.mul_le_mul_left (6000*r.U*(r.U+1)) hqq
  have hone : 1≤(r.U+1)^2*q^2 := by
    have hpos : 0<(r.U+1)^2*q^2 := by positivity
    omega
  rw [pass_cost]
  change 2*r.Gates*linear r+2*r.Used*bucket r+16≤10^9*(r.U+1)^2*q^2
  nlinarith

theorem bank_budget (r : Request) : MatrixBatchBucketBank.budget r≤6*10^10*(r.U+1)^2*(r.d+r.p+1)^2 := by
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
  have hc : r.Buckets≤r.U+r.U+1 := by
    unfold Request.Buckets SupplierPrinter.stableDominanceBucketCount
    exact Nat.add_le_add_right (Nat.div_le_self _ _) 1
  have hbase : MatrixBatchRankReverse.budget r≤5*10^10*(r.U+1)^2*q^2 := MatrixBatchRankReverseBounds.budget_le r
  have huq : q≤(r.U+1)^2*q^2 := by
    have hu : 1≤(r.U+1)^2 := by nlinarith
    have h := Nat.mul_le_mul hu hqq
    simpa using h
  have hu : r.U≤(r.U+1)^2*q^2 := by
    have hq2 : 1≤q^2 := by nlinarith
    have h := Nat.mul_le_mul (show r.U≤(r.U+1)^2 by nlinarith) hq2
    simpa using h
  have hd := Nat.mul_le_mul_right (q^2) (show r.U≤(r.U+1)^2 by nlinarith)
  unfold MatrixBatchBucketBank.budget MatrixBatchBucketBank.bankBudget MatrixBucketTemplate.budget
  change MatrixBatchRankReverse.budget r+1+((2*MatrixScoreReusableRanks.D r+4)+1+
    (24*H r+24*r.M+53)+1+(4*r.Buckets+12))≤6*10^10*(r.U+1)^2*q^2
  nlinarith

theorem budget_le (r : Request) : MatrixBatchBucketPass.budget r≤10^11*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have h1 := bank_budget r
  have h2 := pass_budget r
  have hp : 1≤(r.U+1)^2*(r.d+r.p+1)^2 := by
    have hpos : 0<(r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold MatrixBatchBucketPass.budget
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixBatchBucketPassBounds
