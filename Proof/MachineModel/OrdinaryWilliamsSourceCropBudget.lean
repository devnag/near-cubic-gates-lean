import Proof.MachineModel.OrdinaryWilliamsSourceCrop

/-! Full source replay/rewind/crop charge at the arbitrary request size.
The source's logarithmic exponent is retained and the physical output scan
costs one additional power. Input/template construction is still separate. -/
namespace NearCubicWires.RepairOrdinary.WilliamsSourceCrop
open RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem logarithm_padding (u v : ℕ) (hv : v ≤ 1024 * u) : logScale v ≤ logScale u + 10 := by
  have hpow : u + 2 ≤ 2 ^ logScale u := Nat.le_pow_clog (by decide) (u + 2)
  apply Nat.clog_le_of_le_pow
  calc
    v + 2 ≤ 1024 * (u + 2) := by omega
    _ ≤ 1024 * 2 ^ logScale u := Nat.mul_le_mul_left 1024 hpow
    _ = 2 ^ (logScale u + 10) := by rw [pow_add]; norm_num; ring

theorem bitlength_log (u : ℕ) : natBitLength u + 1 ≤ logScale u + 2 := by
  have h0 := Nat.log_le_clog 2 u
  have h1 := Nat.clog_mono_right 2 (show u ≤ u + 2 by omega)
  dsimp only [natBitLength, logScale]
  omega

def coefficient (a : WilliamsAlgorithm) : ℕ := 2097152 * a.coefficient * 11 ^ a.logExponent + 53251

theorem whole_budget (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    budget a r hr ≤ coefficient a * (r.dimension + 1) ^ 2 * (logScale r.dimension + 1) ^ (a.logExponent + 1) := by
  let u := r.dimension
  let v := WilliamsPaddedRequest.dimension u
  let q := logScale u + 1
  let square := (u + 1) ^ 2
  let P := square * q ^ (a.logExponent + 1)
  have hv : v ≤ 1024 * u := WilliamsPaddedRequest.dimension_le u hr
  have hlu : logScale v ≤ 11 * q := by
    have h := logarithm_padding u v hv
    dsimp only [q]
    omega
  have hw : natBitLength v + 1 ≤ 13 * q := by
    have h := bitlength_log v
    have h' := logarithm_padding u v hv
    dsimp only [q]
    omega
  have hv2 : v ^ 2 ≤ 1048576 * square := by
    have h := Nat.pow_le_pow_left (show v ≤ 1024 * (u + 1) by omega) 2
    simpa [square, mul_pow] using h
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hpow : q ^ a.logExponent ≤ q ^ (a.logExponent + 1) := Nat.pow_le_pow_right hq (by omega)
  have hqpow : q ≤ q ^ (a.logExponent + 1) := Nat.le_self_pow (by omega) q
  have hsource : WilliamsReplay.budget a (WilliamsPaddedRequest.request r hr) ≤
      1048576 * a.coefficient * 11 ^ a.logExponent * P := by
    change a.coefficient * v ^ 2 * logScale v ^ a.logExponent ≤ _
    calc
      _ ≤ a.coefficient * (1048576 * square) * (11 * q) ^ a.logExponent := by gcongr
      _ = 1048576 * a.coefficient * 11 ^ a.logExponent * (square * q ^ a.logExponent) := by rw [mul_pow]; ring
      _ ≤ _ := by dsimp only [P]; gcongr
  have hcrop : WilliamsCrop.budget u v (natBitLength v) ≤ 53248 * P := by
    have h := WilliamsCrop.budget_quadratic u v (natBitLength v) (WilliamsPaddedRequest.dimension_ge u) hv
    calc
      _ ≤ 4096 * square * (natBitLength v + 1) := h
      _ ≤ 4096 * square * (13 * q) := Nat.mul_le_mul_left _ hw
      _ = 53248 * (square * q) := by ring
      _ ≤ _ := by dsimp only [P]; gcongr
  have hpositive : 1 ≤ P := by
    dsimp only [P, square]
    exact Nat.mul_pos (by positivity) (pow_pos (by omega) _)
  change 2 * WilliamsReplay.budget a (WilliamsPaddedRequest.request r hr) +
    WilliamsCrop.budget u v (natBitLength v) + 3 ≤ coefficient a * square * q ^ (a.logExponent + 1)
  have he : coefficient a * square * q ^ (a.logExponent + 1) =
      (2 * (1048576 * a.coefficient * 11 ^ a.logExponent) + 53251) * P := by
    dsimp only [coefficient, P]
    ring
  rw [he]
  nlinarith

end NearCubicWires.RepairOrdinary.WilliamsSourceCrop
