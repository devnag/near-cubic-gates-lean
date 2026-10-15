import Proof.MachineModel.OrdinaryMatrixBatchLeftPlane

/-! Whole original-request left-plane cost. The ordinary sorting and
literal padded row traversal use Used≤Capacity≤U, preserving the required
quadratic dependence on the assignment half-table size. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchLeftPlaneBounds
open MatrixScoreBatch MatrixBucketLeftPlane
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem left_fields_le (r : Request) :
    (MatrixRows.fields (GridRows.leftRows r.M r.M (MatrixBucketCrossGrid.payload r))).length≤
      r.Used*(r.U+r.U)*(4*r.M+3)+1 := by
  have hg := GridRows.grid_split r.M r.M (MatrixBucketCrossGrid.payload r)
  have hlen : (StablePartition.stream (CoordinateKey.grid r.M r.M (MatrixBucketCrossGrid.payload r))).length=
      r.Used*(r.U+r.U)*(4*r.M+3)+1 := by
    rw [← MatrixBucketCrossGrid.sorted_grid,SortMatrix.sorted_stream_length]
    change (StablePartition.stream (MatrixBucketKeyRecords.records r)).length=_
    rw [SortCost.stream_length_of_width _ _ (MatrixBucketKeyRecords.width r),MatrixBucketKeyRecords.count]
    congr 2
    omega
  have hf : (MatrixRows.fields (GridRows.leftRows r.M r.M (MatrixBucketCrossGrid.payload r))).length≤
      (StablePartition.stream (CoordinateKey.grid r.M r.M (MatrixBucketCrossGrid.payload r))).length := by
    rw [StablePartition.stream,hg,List.length_append,List.length_append]
    omega
  exact hf.trans_eq hlen

theorem sort_budget_le (r : Request) : MatrixBucketCoordinateSort.budget r≤
    100000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let q := r.d+r.p+1
  have hq : 1≤q := by dsimp [q]; omega
  have hm : r.M+r.M+2≤8*q := by rw [common_width]; dsimp [q]; omega
  have hu : r.Used≤r.U := (MatrixScoreBatch.capacity r).trans (WilliamsPaddedRequest.inner_le r.U)
  have hn : r.Used*(r.U+r.U)+1≤2*(r.U+1)^2 := by nlinarith
  have hs := MatrixBucketCoordinateSort.budget_le r
  have hw : (r.M+r.M+2)^2≤64*q^2 := by nlinarith
  have hb := Nat.mul_le_mul hn hw
  have hp : 1≤(r.U+1)^2*q^2 := by
    have hpos : 0<(r.U+1)^2*q^2 := by positivity
    omega
  change MatrixBucketCoordinateSort.budget r≤100000*(r.U+1)^2*q^2
  nlinarith

theorem plane_budget_le (r : Request) : MatrixBucketLeftPlane.budget r≤
    1000*(r.U+1)^2*(r.d+r.p+1)^2 := by
  let q := r.d+r.p+1
  have hq : 1≤q := by dsimp [q]; omega
  have hqq : q≤q^2 := by nlinarith
  have hm : 4*r.M+3≤15*q := by rw [common_width]; dsimp [q]; omega
  have hcap : r.Capacity≤r.U := WilliamsPaddedRequest.inner_le r.U
  have hu : r.Used≤r.U := (MatrixScoreBatch.capacity r).trans hcap
  have hpad : r.Capacity-r.Used≤r.U := by omega
  have hn : r.Used*(r.U+r.U)≤2*r.U^2 := by nlinarith
  have hmul := Nat.mul_le_mul hn hm
  have hfields := left_fields_le r
  have hrow := Nat.mul_le_mul_left r.U (show 3*r.Used+2*(r.Capacity-r.Used)+11≤5*r.U+11 by omega)
  have hbig := Nat.mul_le_mul_left (30*r.U^2) hqq
  have hp : 1≤(r.U+1)^2*q^2 := by
    have hpos : 0<(r.U+1)^2*q^2 := by positivity
    omega
  have huq := Nat.mul_le_mul_left ((r.U+1)^2) (show 1≤q^2 by nlinarith)
  unfold MatrixBucketLeftPlane.budget forwardBudget rowBudget
  change 2*((MatrixRows.fields (GridRows.leftRows r.M r.M (MatrixBucketCrossGrid.payload r))).length+
    r.U*(3*r.Used+2*(r.Capacity-r.Used)+11)+1+2)+2≤1000*(r.U+1)^2*q^2
  nlinarith

theorem budget_le (r : Request) : MatrixBatchLeftPlane.budget r≤
    2*10^11*(r.U+1)^2*(r.d+r.p+1)^2 := by
  have hbase := MatrixBatchBucketPassBounds.budget_le r
  have hsort := sort_budget_le r
  have hplane := plane_budget_le r
  have hp : 1≤(r.U+1)^2*(r.d+r.p+1)^2 := by
    have hpos : 0<(r.U+1)^2*(r.d+r.p+1)^2 := by positivity
    omega
  unfold MatrixBatchLeftPlane.budget MatrixBatchCoordinateSort.budget
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixBatchLeftPlaneBounds
