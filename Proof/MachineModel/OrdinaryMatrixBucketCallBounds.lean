import Proof.MachineModel.OrdinaryMatrixBucketBankNative

/-! Bounds for the literal bucket call, derived from the original Request.
They cover every bucket increment and every indexed rank, including the
final increment executed by the existing ordinary controller. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketCallBounds
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entries_length (r : Request) (gate : Fin r.Gates) :
    (MatrixScoreRawRanks.entries r gate).length=r.U+r.U := by
  simpa only [MatrixBatchRankedGate.rankWords,List.length_map] using MatrixBatchRankedGate.words_length r gate

theorem native_power (r : Request) : 2^r.M=8*r.U := by
  rw [common_width]
  simp [Request.U,Nat.pow_add,Nat.mul_comm]

theorem header_power (r : Request) : 16*r.U ≤ 2^(H r) := by
  have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show r.M+1 ≤ H r by unfold H; omega)
  rw [Nat.pow_succ,native_power] at h
  nlinarith

theorem ranks_fit (r : Request) (gate : Fin r.Gates) :
    ∀ entry∈MatrixScoreRawRanks.entries r gate,entry.2.2<2^(H r) := by
  apply KeyLoop.indexed_fits
  have hl := entries_length r gate
  simp only [MatrixScoreRawRanks.entries,KeyLoop.indexed_length] at hl
  have hp := header_power r
  have hu : 1 ≤ r.U := Nat.one_le_two_pow
  omega

theorem boundary_le (r : Request) : r.Buckets*(r.bucketSize+1) ≤ 4*r.U+1 := by
  have hd := Nat.div_mul_le_self (r.U+r.U) (r.bucketSize+1)
  have hb : r.bucketSize+1 ≤ 2*r.U+1 := MatrixBucketDimensions.width_le r.U r.Gates
  unfold Request.Buckets SupplierPrinter.stableDominanceBucketCount
  nlinarith

theorem boundary_fit (r : Request) : r.Buckets*(r.bucketSize+1)<2^(H r) := by
  have hb := boundary_le r
  have hp := header_power r
  have hu : 1 ≤ r.U := Nat.one_le_two_pow
  omega

theorem inner_fit (r : Request) (gate : Fin r.Gates) : gate.val*r.Buckets+r.Buckets<2^r.M := by
  have hgate : gate.val+1 ≤ r.Gates := by omega
  have hm := Nat.mul_le_mul_right r.Buckets hgate
  have hc := capacity r
  have hu : r.Capacity ≤ r.U := WilliamsPaddedRequest.inner_le r.U
  have hpos : 1 ≤ r.U := Nat.one_le_two_pow
  unfold Request.Used at hc
  rw [native_power]
  nlinarith

def resetBudget (r : Request) := (r.U+r.U)*(68*H r+8*r.M+63)+1

theorem reset_fit (r : Request) : resetBudget r ≤ MatrixScoreReusableRanks.D r := by
  have hcap := MatrixScoreReusableRanks.capacity_gap r
  have hw := MatrixScoreRawRanksBounds.header_width r
  have hq : r.d+r.p+1 ≤ (r.d+r.p+1)^2 := by nlinarith
  have hh : 68*H r+8*r.M+63 ≤ 671*(r.d+r.p+1) := by unfold H; omega
  have hm := Nat.mul_le_mul_left (r.U+r.U) hh
  have hsq := Nat.mul_le_mul_left (r.U+r.U) hq
  unfold resetBudget MatrixScoreRawRanksBounds.capacity at *
  nlinarith

theorem workspace_fit (r : Request) : 24*H r+14 ≤ MatrixScoreReusableRanks.D r := by
  have hreset := reset_fit r
  have hu : 1 ≤ r.U := Nat.one_le_two_pow
  have hp := Nat.mul_le_mul_right (68*H r+8*r.M+63) hu
  unfold resetBudget at hreset
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixBucketCallBounds
