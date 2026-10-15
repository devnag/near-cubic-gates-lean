import Proof.MachineModel.OrdinaryMatrixVariablePacketWorkspace
import Proof.MachineModel.OrdinaryMatrixVariableCapacity

/-! The entire packet includes physical dimension construction, append,
and reset. Its envelope pays all of them, retaining the source exponent. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariablePacketBounds
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem arithmetic_bound (base C U d bit q E : ℕ) (hq : 1≤q) (hE : 1≤E)
    (hd : d+1≤q) (hbit : bit≤q) (hb : base≤C*(U+1)^2*q^E) :
    base+8*U^2*(d+1)+10*U^2+10*U+6*d+4*bit+71≤(C+128)*(U+1)^2*q^E := by
  let B := (U+1)^2*q^E
  have hpower : q≤q^E := Nat.le_self_pow (by omega) _
  have hqB : q≤B := hpower.trans (Nat.le_mul_of_pos_left _ (pow_pos (Nat.zero_lt_succ U) 2))
  have hB : 1≤B := hq.trans hqB
  have hU2 : U^2≤B := (Nat.pow_le_pow_left (by omega : U≤U+1) 2).trans
    (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hU : U≤B := (show U≤(U+1)^2 by nlinarith).trans
    (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hn : U^2*(d+1)≤B := Nat.mul_le_mul
    (Nat.pow_le_pow_left (by omega : U≤U+1) 2) (hd.trans hpower)
  rw [Nat.mul_assoc] at hb
  change base≤C*B at hb
  calc
    _ ≤ (C+128)*B := by nlinarith only [hb,hn,hU2,hU,hd,hbit,hqB,hB]
    _ = _ := by dsimp [B]; ring

def coefficient (a : WilliamsAlgorithm) := MatrixWilliamsProductBounds.coefficient a+128
def exponent (a : WilliamsAlgorithm) := MatrixWilliamsProductBounds.exponent a

theorem budget_eq (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) :
    MatrixVariablePacket.budget a r bit negative=MatrixVariableProduct.budget a r+
      8*r.U^2*(r.d+1)+10*r.U^2+10*r.U+6*r.d+4*bit+71 := by
  unfold MatrixVariablePacket.budget MatrixVariableCount.budget MatrixPacketDimensions.budget MatrixPacketDock.budget
  rw [MatrixVariableCount.native_length]
  ring

theorem budget_bound (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) (ht : bit<r.p) :
    MatrixVariablePacket.budget a r bit negative≤coefficient a*(r.U+1)^2*(r.d+r.p+1)^exponent a := by
  rw [budget_eq]
  apply arithmetic_bound (C := MatrixWilliamsProductBounds.coefficient a)
  · omega
  · unfold exponent MatrixWilliamsProductBounds.exponent
    omega
  · omega
  · omega
  · simpa only [MatrixVariableProduct.budget_eq,exponent] using MatrixWilliamsProductBounds.budget_bound a r

end NearCubicWires.RepairOrdinary.MatrixVariablePacketBounds
