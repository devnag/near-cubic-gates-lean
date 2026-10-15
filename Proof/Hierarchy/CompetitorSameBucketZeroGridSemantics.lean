import Proof.Hierarchy.CompetitorSameBucketZeroGrid

/-! The executed nested zero-grid stream is exactly the existing canonical
row-major zero-record list, with its full quadratic time ledger. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroGrid
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_range (p m left start n : ℕ) : CompetitorSameBucketZeroRow.bits p m left start n=
    (List.range' start n).flatMap (CompetitorSameBucketKeyAppend.word p m 0 left) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [CompetitorSameBucketZeroRow.bits,List.range'_succ,ih]

theorem grid_range (p m u left n : ℕ) : bits p m u left n=
    (List.range' left n).flatMap (fun row => CompetitorSameBucketZeroRow.bits p m row u u) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simp [bits,List.range'_succ,ih]

theorem finRange_flatMap {α : Type} (n : ℕ) (f : ℕ → List α) :
    (List.finRange n).flatMap (fun i => f i.val)=(List.range n).flatMap f := by
  rw [←List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map]

theorem zero_records (p m u : ℕ) : bits p m u 0 u=
    (CompetitorSameBucketKeys.zeroRecords p m u).flatMap (fun e => frame (RadixSemantics.word e)) := by
  rw [grid_range]
  simp only [row_range,List.range'_eq_map_range,List.flatMap_map,Nat.zero_add]
  unfold CompetitorSameBucketKeys.zeroRecords
  simp only [List.flatMap_assoc,List.flatMap_map]
  change (List.range u).flatMap (fun row => (List.range u).flatMap (fun col => CompetitorSameBucketKeyAppend.word p m 0 row (u+col)))=
    (List.finRange u).flatMap (fun row => (List.finRange u).flatMap
      (fun col => CompetitorSameBucketKeyAppend.word p m 0 row.val (u+col.val)))
  calc
    _=(List.finRange u).flatMap (fun row => (List.range u).flatMap
        (fun col => CompetitorSameBucketKeyAppend.word p m 0 row.val (u+col))) :=
      (finRange_flatMap u (fun row => (List.range u).flatMap
        (fun col => CompetitorSameBucketKeyAppend.word p m 0 row (u+col)))).symm
    _=_ := by
      apply congrArg (List.flatMap · (List.finRange u))
      funext row
      exact (finRange_flatMap u (fun col => CompetitorSameBucketKeyAppend.word p m 0 row.val (u+col))).symm

theorem budget_bound (p m u cap : ℕ) : budget p m u cap u≤100*(u^2+1)*(cap+p+m+1) := by
  have h : u≤u^2+1 := by nlinarith
  have h0:=Nat.mul_le_mul_right cap h
  have h1:=Nat.mul_le_mul_right m h
  have h2:=Nat.mul_le_mul_right p h
  unfold budget CompetitorSameBucketZeroBody.budget CompetitorSameBucketZeroRow.budget
    CompetitorSameBucketZeroCell.budget CompetitorSameBucketZeroFinish.budget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroGrid
