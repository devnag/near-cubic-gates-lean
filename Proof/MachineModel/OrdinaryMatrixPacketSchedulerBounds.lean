import Proof.MachineModel.OrdinaryMatrixPacketController
import Proof.MachineModel.OrdinaryMatrixPacketBudget

/-! Final source-fixed accounting for the actual cold scheduler. The
extra q factor pays all p pairs; one global rewind and support are paid. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketSchedulerBounds
open MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev E (a : WilliamsAlgorithm) := MatrixPacketBudget.exponent a
abbrev C (a : WilliamsAlgorithm) := MatrixPacketBudget.coefficient a
def coefficient (a : WilliamsAlgorithm) := (40*E a+1024)*C a
def exponent (a : WilliamsAlgorithm) := E a+1
def envelope (a : WilliamsAlgorithm) (r : Request) := coefficient a*(r.U+1)^2*(r.d+r.p+1)^exponent a

theorem coefficient_positive (a : WilliamsAlgorithm) : 0<coefficient a :=
  Nat.mul_pos (by omega) (Nat.lt_of_lt_of_le Nat.zero_lt_one (MatrixPacketBudget.coefficient_pos a))
theorem exponent_paid (a : WilliamsAlgorithm) : a.logExponent≤exponent a := by
  unfold exponent E MatrixPacketBudget.exponent MatrixVariablePacketCapacity.exponent MatrixVariablePacketBounds.exponent MatrixWilliamsProductBounds.exponent
  omega

theorem envelope_eq (a : WilliamsAlgorithm) (r : Request) :
    envelope a r=(40*E a+1024)*MatrixPacketBudget.capacity a r*(r.d+r.p+1) := by
  unfold envelope coefficient exponent MatrixPacketBudget.capacity MatrixVariablePacketCapacity.capacity
  rw [pow_succ]
  ring

theorem raw_bound (a : WilliamsAlgorithm) (r : Request) :
    MatrixPacketController.budget a (E a) (C a) r≤
      (20*E a+410)*MatrixPacketBudget.capacity a r*(r.d+r.p+1) := by
  have hq:=MatrixPacketBudget.q_le a r
  have hc : 1≤MatrixPacketBudget.capacity a r := by omega
  have hmul:=Nat.le_mul_of_pos_right (MatrixPacketBudget.capacity a r) (by omega : 1≤r.d+r.p+1)
  have hh:=(MatrixPacketBudget.input_header_le a r).2
  by_cases hz : r.p=0
  · unfold MatrixPacketController.budget
    rw [if_pos hz]
    nlinarith only [hh,hc,hmul]
  · have hp : 0<r.p := by omega
    have hpbound:=MatrixPacketBudget.positive_bound a r hp
    unfold MatrixPacketController.budget MatrixPacketBranch.budget
    rw [if_neg hz]
    nlinarith only [hh,hc,hmul,hpbound]

theorem final_bounds (a : WilliamsAlgorithm) (r : Request) :
    2*MatrixPacketController.budget a (E a) (C a) r+3≤envelope a r ∧
    (physicalInput r).length≤envelope a r := by
  have hb:=raw_bound a r
  have hq:=MatrixPacketBudget.q_le a r
  have hc : 1≤MatrixPacketBudget.capacity a r := by omega
  have hmul:=Nat.le_mul_of_pos_right (MatrixPacketBudget.capacity a r) (by omega : 1≤r.d+r.p+1)
  have hi:=(MatrixPacketBudget.input_header_le a r).1
  rw [envelope_eq]
  constructor <;> nlinarith only [hb,hq,hc,hmul,hi]

end NearCubicWires.RepairOrdinary.MatrixPacketSchedulerBounds
