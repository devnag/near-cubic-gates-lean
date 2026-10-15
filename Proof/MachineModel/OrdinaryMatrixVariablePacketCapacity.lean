import Proof.MachineModel.OrdinaryMatrixVariablePacketBounds

/-! Source-fixed clear capacity for the complete physical packet body,
including its dimension production, append and paid local reset. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariablePacketCapacity
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient (a : WilliamsAlgorithm) := 4*MatrixVariablePacketBounds.coefficient a+16
def exponent (a : WilliamsAlgorithm) := MatrixVariablePacketBounds.exponent a
def capacity (a : WilliamsAlgorithm) (r : Request) := coefficient a*(r.U+1)^2*(r.d+r.p+1)^exponent a

theorem capacity_bound (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) (ht : bit<r.p) :
    MatrixVariablePacketWorkspace.footprint a r bit negative≤capacity a r := by
  let B := (r.U+1)^2*(r.d+r.p+1)^exponent a
  have hq : 1≤r.d+r.p+1 := by omega
  have hqB : r.d+r.p+1≤B := by
    have hp : r.d+r.p+1≤(r.d+r.p+1)^exponent a := Nat.le_self_pow
      (by unfold exponent MatrixVariablePacketBounds.exponent MatrixWilliamsProductBounds.exponent; omega) _
    have hu : 1≤(r.U+1)^2 := pow_pos (Nat.zero_lt_succ r.U) 2
    exact hp.trans (Nat.le_mul_of_pos_left _ hu)
  have hB : 1≤B := hq.trans hqB
  have hb : MatrixVariablePacket.budget a r bit negative≤MatrixVariablePacketBounds.coefficient a*B := by
    simpa only [B,exponent,Nat.mul_assoc] using MatrixVariablePacketBounds.budget_bound a r negative bit ht
  have hi : (physicalInput r).length≤MatrixVariablePacket.budget a r bit negative := by
    have h := MatrixVariableCapacity.input_bound r
    rw [MatrixVariablePacketBounds.budget_eq]
    unfold MatrixVariableProduct.budget
    rw [MatrixVariableInput.budget_eq]
    omega
  have hc : 1≤MatrixVariablePacketBounds.coefficient a := by
    unfold MatrixVariablePacketBounds.coefficient
    omega
  have hmul : B≤MatrixVariablePacketBounds.coefficient a*B := Nat.le_mul_of_pos_left _ hc
  unfold MatrixVariablePacketWorkspace.footprint MatrixVariablePacketReset.budget
  have he : capacity a r=(4*MatrixVariablePacketBounds.coefficient a+16)*B := by
    unfold capacity coefficient
    dsimp [B]
    ring
  rw [he]
  nlinarith only [hi,hb,hqB,hB,hmul]

end NearCubicWires.RepairOrdinary.MatrixVariablePacketCapacity
