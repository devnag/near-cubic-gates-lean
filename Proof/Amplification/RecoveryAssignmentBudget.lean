import Proof.Amplification.RecoveryAssignment

/-! Query-width bounds for the actual assignment machine and its reusable
scratch. Counts in the committed prefix stay binary throughout. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open RecoveryValuationStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem assignment_budget (d : Data) (binaryCount committed : List Bool) (guard : Bool)
    (hi : d.index.length=d.width) (hc : binaryCount.length=d.width)
    (hm : committed.length≤d.width) :
    cost d (3*(d.width+1)) binaryCount committed guard≤128*(d.width+1)^2 := by
  have hmul := Nat.mul_le_mul_right (4*d.width+9) hm
  simp only [cost,RecoveryValuationCount.limit,budget,RecoveryPrefixAssignment.cost,prefixData,
    RecoveryCommittedBit.rawCost,hi,hc]
  nlinarith

theorem committed_budget (index committed : List Bool) (width : Nat)
    (hi : index.length=width) (hm : committed.length≤width) :
    RecoveryCommittedBit.rawCost index committed≤5*(width+1)^2 := by
  have hmul := Nat.mul_le_mul_right (4*width+9) hm
  simp only [RecoveryCommittedBit.rawCost,hi]
  nlinarith

theorem scratch_fits (width : Nat) :
    3*(width+1)+1≤8192*(width+1)^2 ∧
    2*width+3≤8192*(width+1)^2 ∧
    128*(width+1)^2+3≤8192*(width+1)^2 := by
  have hpos : 0<(width+1)^2 := by positivity
  have hs : 1≤(width+1)^2 := hpos
  constructor
  · nlinarith
  constructor <;> nlinarith

end NearCubicWires.RepairOrdinary.RecoveryAssignment
