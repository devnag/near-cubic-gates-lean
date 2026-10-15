import Proof.MachineModel.OrdinaryMatrixWilliamsProductEnvelope

/-! The complete explicit preprocessing/source call has a uniform quadratic
assignment-table envelope. This is the physical clear capacity supplier for
repeating the cold call, with the source logarithmic exponent retained. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsProductBounds
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem arithmetic_bound (base u q z c e : ℕ) (hu : 1≤u) (hq : 1≤q)
    (hb : base≤1000000000000*u^2*q^2) (hz : z≤3*q) :
    base+1+(2*(c*u^2*z^(e+1))+2)≤(1000000000000+2*c*3^(e+1)+3)*u^2*q^(e+3) := by
  let B := u^2*q^(e+3)
  have hp2 : q^2≤q^(e+3) := Nat.pow_le_pow_right hq (by omega)
  have hpe : q^(e+1)≤q^(e+3) := Nat.pow_le_pow_right hq (by omega)
  have hb' : base≤1000000000000*B := by
    calc
      _ ≤ 1000000000000*u^2*q^2 := hb
      _ ≤ 1000000000000*u^2*q^(e+3) := Nat.mul_le_mul_left _ hp2
      _ = _ := Nat.mul_assoc _ _ _
  have hp : z^(e+1)≤3^(e+1)*q^(e+3) := by
    calc
      _ ≤ (3*q)^(e+1) := Nat.pow_le_pow_left hz _
      _ = 3^(e+1)*q^(e+1) := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ hpe
  have hs : 2*(c*u^2*z^(e+1))≤(2*c*3^(e+1))*B := by
    calc
      _ ≤ 2*(c*u^2*(3^(e+1)*q^(e+3))) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (c*u^2) hp)
      _ = _ := by dsimp [B]; ring
  have hB : 1≤B := Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
  calc
    _ ≤ (1000000000000+2*c*3^(e+1)+3)*B := by nlinarith only [hb',hs,hB]
    _ = _ := by dsimp [B]; ring

theorem budget_bound (a : WilliamsAlgorithm) (r : Request) : MatrixWilliamsProduct.budget a r≤
    coefficient a*(r.U+1)^2*(r.d+r.p+1)^exponent a := by
  exact arithmetic_bound (MatrixWilliamsInput.budget r) (r.U+1) (r.d+r.p+1)
    (logScale r.U+1) (WilliamsCall.coefficient a) a.logExponent
    (by omega) (by omega) (preparation_bound r) (log_bound r)

end NearCubicWires.RepairOrdinary.MatrixWilliamsProductBounds
