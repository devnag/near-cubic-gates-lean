import Proof.Hierarchy.CompetitorCrossScheduler

/-! The entire original-request-to-cross-bank runtime preserves the
Williams source exponent plus the already paid four preprocessing powers.
The literal short-width capacity and cold initialization are included. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
open RepairRepresentation MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coefficient (a : WilliamsAlgorithm) := (supplier a).coefficient+375005003
def exponent (a : WilliamsAlgorithm) := a.logExponent+4
noncomputable def envelope (a : WilliamsAlgorithm) (r : Request) :=
  coefficient a*(r.U+1)^2*(r.d+r.p+1)^exponent a

theorem exponent_eq (a : WilliamsAlgorithm) : (supplier a).exponent=exponent a := by
  change MatrixPacketSchedulerBounds.exponent a=a.logExponent+4
  unfold MatrixPacketSchedulerBounds.exponent MatrixPacketSchedulerBounds.E MatrixPacketBudget.exponent
    MatrixVariablePacketCapacity.exponent MatrixVariablePacketBounds.exponent MatrixWilliamsProductBounds.exponent
  omega

theorem budget_bound (a : WilliamsAlgorithm) (r : Request) : budget a r+1 ≤ envelope a r := by
  let mass := (r.U+1)^2*(r.d+r.p+1)^exponent a
  have h2 : (r.d+r.p+1)^2 ≤ (r.d+r.p+1)^exponent a :=
    Nat.pow_le_pow_right (by omega) (by unfold exponent;omega)
  have h3 : (r.d+r.p+1)^3 ≤ (r.d+r.p+1)^exponent a :=
    Nat.pow_le_pow_right (by omega) (by unfold exponent;omega)
  have f := (CompetitorCrossRequestFields.budget_bound r).trans
    (Nat.mul_le_mul_left (5000*(r.U+1)^2) h2)
  have c := (CompetitorCrossTableCold.request_bound r).trans
    (Nat.mul_le_mul_left (375000000*(r.U+1)^2) h3)
  have hpos : 1 ≤ mass := by
    have h : 0 < mass := by dsimp [mass];positivity
    omega
  have hs : schedulerBudget a r=(supplier a).coefficient*mass := by
    unfold schedulerBudget
    rw [exponent_eq]
    dsimp [mass]
    ring
  rw [Nat.mul_assoc] at f c
  change CompetitorCrossRequestFields.budget r ≤ 5000*((r.U+1)^2*(r.d+r.p+1)^exponent a) at f
  change CompetitorCrossTableCold.budget (natBitLength r.U)
    (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p ≤
      375000000*((r.U+1)^2*(r.d+r.p+1)^exponent a) at c
  unfold budget prefixBudget envelope coefficient
  rw [hs,Nat.mul_assoc]
  change CompetitorCrossRequestFields.budget r+1+(supplier a).coefficient*mass+1+
    CompetitorCrossTableCold.budget (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p+1 ≤
    ((supplier a).coefficient+375005003)*mass
  change CompetitorCrossRequestFields.budget r ≤ 5000*mass at f
  change CompetitorCrossTableCold.budget (natBitLength r.U)
    (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p ≤ 375000000*mass at c
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
