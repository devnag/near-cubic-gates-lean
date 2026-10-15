import Proof.MachineModel.OrdinaryMatrixSignedEntry

namespace NearCubicWires.RepairOrdinary.MatrixSignedMaskBounds
open MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (r : Request) := 128*(r.U+1)^2*(r.p+1)

theorem budget_eq (r : Request) : MatrixSignedMaskPass.budget r=
    8*r.Gates*r.p+44*r.Gates+4*r.Capacity+4*r.U*r.Capacity+14*r.U+36 := by
  have hh := Nat.add_sub_of_le (MatrixScoreBatch.capacity r)
  change r.Gates*r.Buckets+(r.Capacity-r.Used)=r.Capacity at hh
  unfold MatrixSignedMaskPass.budget MatrixSignedMaskPrepare.budget MatrixCoefficientBitPass.budget
    MatrixCoefficientBitNative.budget MatrixMaskPad.budget MatrixMaskPad.forwardBudget MatrixMaskExpand.nativeBudget
    MatrixSignedPlane.budget MatrixMaskAndPass.budget MatrixMaskAndLoop.nativeBudget
  nlinarith

theorem budget_le (r : Request) : MatrixSignedMaskPass.budget r≤capacity r := by
  have hg : r.Gates≤r.U := (Nat.le_mul_self r.Gates).trans
    (r.gateSquare.trans (WilliamsPaddedRequest.inner_le r.U))
  have hc : r.Capacity≤r.U := WilliamsPaddedRequest.inner_le r.U
  have hp := Nat.mul_le_mul_right r.p hg
  have hu := Nat.mul_le_mul_left r.U hc
  have hw : r.U≤(r.U+1)^2 := by nlinarith
  have hwp := Nat.mul_le_mul_right r.p hw
  rw [budget_eq]
  unfold capacity
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixSignedMaskBounds
