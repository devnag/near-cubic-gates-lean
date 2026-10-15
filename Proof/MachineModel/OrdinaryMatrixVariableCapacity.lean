import Proof.MachineModel.OrdinaryMatrixVariableWorkspace
import Proof.MachineModel.OrdinaryMatrixWilliamsProductBounds

namespace NearCubicWires.RepairOrdinary.MatrixVariableCapacity
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_bound (r : Request) : (physicalInput r).length≤MatrixWilliamsInput.budget r := by
  have hc : (physicalInput r).length≤MatrixCoefficientCold.budget r := by
    have hw : natWord r.d++(natWord r.p++(natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++
        r.cuts.flatMap (cutWord r.p)))=word r := by
      simp only [word,header,List.append_assoc]
    unfold MatrixCoefficientCold.budget MatrixCoefficientCold.forwardBudget MatrixCoefficientHeaders.budget
      MatrixScoreHeaders.budget WilliamsInputHeader.budget
    rw [hw]
    simp only [physicalInput,frame_length]
    omega
  rw [MatrixWilliamsProductBounds.preparation_eq]
  unfold MatrixBatchCoefficientPlanes.budget
  omega

def coefficient (a : WilliamsAlgorithm) := 4*MatrixWilliamsProductBounds.coefficient a+16
def exponent (a : WilliamsAlgorithm) := MatrixWilliamsProductBounds.exponent a
def capacity (a : WilliamsAlgorithm) (r : Request) := coefficient a*(r.U+1)^2*(r.d+r.p+1)^exponent a

theorem capacity_bound (a : WilliamsAlgorithm) (r : Request) : MatrixVariableWorkspace.footprint a r≤capacity a r := by
  let B := (r.U+1)^2*(r.d+r.p+1)^exponent a
  have hq : 1≤r.d+r.p+1 := by omega
  have hqB : r.d+r.p+1≤B := by
    have hp : r.d+r.p+1≤(r.d+r.p+1)^exponent a := Nat.le_self_pow (by unfold exponent MatrixWilliamsProductBounds.exponent; omega) _
    have hu : 1≤(r.U+1)^2 := pow_pos (Nat.zero_lt_succ r.U) 2
    exact hp.trans (Nat.le_mul_of_pos_left _ hu)
  have hB : 1≤B := hq.trans hqB
  have hb : MatrixVariableProduct.budget a r≤MatrixWilliamsProductBounds.coefficient a*B := by
    have h := MatrixWilliamsProductBounds.budget_bound a r
    simpa only [MatrixVariableProduct.budget_eq,B,exponent,Nat.mul_assoc] using h
  have hi : (physicalInput r).length≤MatrixVariableProduct.budget a r := by
    have h := input_bound r
    unfold MatrixVariableProduct.budget
    rw [MatrixVariableInput.budget_eq]
    omega
  have hc : 1≤MatrixWilliamsProductBounds.coefficient a := by
    unfold MatrixWilliamsProductBounds.coefficient
    omega
  have hmul : B≤MatrixWilliamsProductBounds.coefficient a*B := Nat.le_mul_of_pos_left _ hc
  unfold MatrixVariableWorkspace.footprint MatrixVariableReset.budget
  change (physicalInput r).length+2*r.p+(2*MatrixVariableProduct.budget a r+2)+4≤_
  have he : capacity a r=(4*MatrixWilliamsProductBounds.coefficient a+16)*B := by
    unfold capacity coefficient
    dsimp [B]
    ring
  rw [he]
  nlinarith only [hi,hb,hqB,hB,hmul]

end NearCubicWires.RepairOrdinary.MatrixVariableCapacity
