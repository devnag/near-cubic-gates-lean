import Proof.CaseAnalysis.WitnessPolicy
import Proof.PCP.ProjectionDimensionDyadic

/-! Exact arithmetic for the existing family policy. Fixed rational data is
represented by its numerator and positive denominator; restricted description
caps use a bit-length shift and never materialize the exponential parameter. -/
namespace NearCubicWires.RepairSource.CloseoutWitnessPolicy
open SourceInterfaces RepairRepresentation RepairOrdinary
open RecoveryWitnessPolicy ComponentwiseCircuitRestriction ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def termFactor (delta : ℚ) (copies : Nat) : ℚ :=
  16 / (delta^2 * epsilonQ delta copies^2)
def termNumerator (delta : ℚ) (copies : Nat) := (termFactor delta copies).num.natAbs
def termDenominator (delta : ℚ) (copies : Nat) := (termFactor delta copies).den
def naturalTermBound (delta : ℚ) (copies n : Nat) :=
  (termNumerator delta copies * n + termDenominator delta copies - 1) /
    termDenominator delta copies

theorem termDenominator_positive (delta : ℚ) (copies : Nat) :
    0 < termDenominator delta copies := (termFactor delta copies).pos

theorem termFactor_nonnegative (delta : ℚ) (copies : Nat) :
    0 ≤ termFactor delta copies := by
  unfold termFactor
  positivity

theorem termFactor_ratio (delta : ℚ) (copies : Nat) :
    (termNumerator delta copies : ℝ) / (termDenominator delta copies : ℝ) =
      (termFactor delta copies : ℝ) := by
  have hn : 0 ≤ (termFactor delta copies).num :=
    Rat.num_nonneg.mpr (termFactor_nonnegative delta copies)
  have he : ((termFactor delta copies).num.natAbs : ℝ) =
      ((termFactor delta copies).num : ℝ) := by
    have hz : ((termFactor delta copies).num.natAbs : ℤ) =
        (termFactor delta copies).num := by
      rw [Int.natCast_natAbs, abs_of_nonneg hn]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hz
  unfold termNumerator termDenominator
  rw [he, Rat.cast_def]

theorem ceil_natural_ratio (a b : Nat) (hb : 0 < b) :
    ⌈(a : ℝ) / (b : ℝ)⌉₊ = (a + b - 1) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hi (m : Nat) : ⌈(a : ℝ) / (b : ℝ)⌉₊ ≤ m ↔ (a + b - 1) / b ≤ m := by
    rw [Nat.ceil_le, div_le_iff₀ hbR, ← Nat.cast_mul, Nat.cast_le,
      Nat.div_le_iff_le_mul_add_pred hb]
    have hm : m * b = b * m := Nat.mul_comm _ _
    omega
  exact Nat.le_antisymm ((hi _).mpr le_rfl) ((hi _).mp le_rfl)

theorem naturalTermBound_exact (delta : ℚ) (copies n : Nat) :
    xorTermBound delta n copies = naturalTermBound delta copies n := by
  have he : 16 * (n : ℝ) / ((delta : ℝ)^2 * xorEpsilon (delta : ℝ) copies^2) =
      ((termNumerator delta copies * n : Nat) : ℝ) /
        (termDenominator delta copies : ℝ) := by
    calc
      _ = (termFactor delta copies : ℝ) * n := by
        simp only [termFactor, Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul,
          Rat.cast_pow, RepairXor.epsilonQ_coe]
        ring
      _ = _ := by
        rw [← termFactor_ratio]
        push_cast
        ring
  unfold xorTermBound
  rw [he, ceil_natural_ratio _ _ (termDenominator_positive delta copies)]
  rfl

theorem restricted_gate_exact (core target L : Nat) :
    restrictedGateDescriptionCap core target (2^L) =
      (core + 1) * (L + natBitLength (target + 1)) + core := by
  unfold restrictedGateDescriptionCap restrictedParameterBound
  rw [Nat.mul_comm (target + 1), DimensionDyadic.bitLength_shift _ _ (by omega)]

theorem symmetric_description_exact (core target W : Nat) :
    restrictedSymmetricDescriptionCap core target (2^symmetricDescriptionCap target W) W =
      (W + 1) * ((core + 1) *
        (symmetricDescriptionCap target W + natBitLength (target + 1)) + core + 1) := by
  unfold restrictedSymmetricDescriptionCap
  rw [restricted_gate_exact]

theorem threshold_description_exact (core target W : Nat) :
    restrictedThresholdDescriptionCap core target (2^thresholdDescriptionCap target W)
      (thresholdDescriptionCap target W) =
      (thresholdDescriptionCap target W + 1) * ((core + 1) *
        (thresholdDescriptionCap target W + natBitLength (target + 1)) + core + 1) := by
  unfold restrictedThresholdDescriptionCap
  rw [restricted_gate_exact]

end
end NearCubicWires.RepairSource.CloseoutWitnessPolicy
