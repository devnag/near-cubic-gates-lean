import Proof.Foundations.AsymptoticAdapters
import Proof.Foundations.CircuitRestriction

/-!
# Physical wire-cap transfer across scheduled padding

The schedule keeps the selected core within a factor three of the target.
Shrinking a source cap coefficient by `27 = 3^3` therefore pays the entire
cubic arity change; monotonicity of `logScale` only improves the comparison.
-/

namespace NearCubicWires.WireScaleTransfer

open NearCubicWires
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.RecoveryPipeline

theorem logScale_mono {core target : ℕ} (hcore : core ≤ target) :
    logScale core ≤ logScale target := by
  apply Nat.clog_mono_right 2
  omega

theorem cube_le_twentySeven_cube {core target : ℕ}
    (hratio : target ≤ 3 * core) :
    target ^ 3 ≤ 27 * core ^ 3 := by
  calc
    target ^ 3 ≤ (3 * core) ^ 3 := Nat.pow_le_pow_left hratio 3
    _ = 27 * core ^ 3 := by ring

theorem cube_le_factor_cube
    (factor : ℕ) {core target : ℕ}
    (hratio : target ≤ factor * core) :
    target ^ 3 ≤ factor ^ 3 * core ^ 3 := by
  calc
    target ^ 3 ≤ (factor * core) ^ 3 :=
      Nat.pow_le_pow_left hratio 3
    _ = factor ^ 3 * core ^ 3 := by ring

/-- Padding through any proved constant-factor arity comparison costs exactly
the cube of that factor.  This is used when a tight source reindexing first
pads a raw recovery core to the linear selector schedule. -/
theorem wireScale_shrink_cube
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient)
    (factor logExponent : ℕ) (hfactor : 0 < factor)
    {core target : ℕ}
    (hcore : core ≤ target) (hratio : target ≤ factor * core) :
    wireScale (coefficient / (factor : ℝ) ^ 3) logExponent target ≤
      wireScale coefficient logExponent core := by
  have hcubeNat := cube_le_factor_cube factor hratio
  have hcubeReal :
      (target : ℝ) ^ 3 ≤ (factor : ℝ) ^ 3 * (core : ℝ) ^ 3 := by
    exact_mod_cast hcubeNat
  have hfactorReal : (0 : ℝ) < factor := by exact_mod_cast hfactor
  have hnumerator :
      coefficient / (factor : ℝ) ^ 3 * (target : ℝ) ^ 3 ≤
        coefficient * (core : ℝ) ^ 3 := by
    calc
      coefficient / (factor : ℝ) ^ 3 * (target : ℝ) ^ 3 ≤
          coefficient / (factor : ℝ) ^ 3 *
            ((factor : ℝ) ^ 3 * (core : ℝ) ^ 3) := by
        gcongr
      _ = coefficient * (core : ℝ) ^ 3 := by
        field_simp
  have hlog := logScale_mono hcore
  have hlogPower :
      (logScale core : ℝ) ^ logExponent ≤
        (logScale target : ℝ) ^ logExponent := by
    gcongr
  have hcoreDenominator :
      0 < (logScale core : ℝ) ^ logExponent := by
    have : (0 : ℝ) < logScale core := by
      exact_mod_cast logScale_pos core
    positivity
  unfold wireScale
  calc
    coefficient / (factor : ℝ) ^ 3 * (target : ℝ) ^ 3 /
          (logScale target : ℝ) ^ logExponent ≤
        coefficient / (factor : ℝ) ^ 3 * (target : ℝ) ^ 3 /
          (logScale core : ℝ) ^ logExponent := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg
          (div_nonneg hcoefficient (by positivity))
          (by positivity))
        hcoreDenominator hlogPower
    _ ≤ coefficient * (core : ℝ) ^ 3 /
          (logScale core : ℝ) ^ logExponent := by
      exact div_le_div_of_nonneg_right hnumerator hcoreDenominator.le

/-- A factor-three arity loss costs exactly the cube of that factor. -/
theorem wireScale_shrink_twentySeven
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient)
    (logExponent : ℕ) {core target : ℕ}
    (hcore : core ≤ target) (hratio : target ≤ 3 * core) :
    wireScale (coefficient / 27) logExponent target ≤
      wireScale coefficient logExponent core := by
  convert
    wireScale_shrink_cube hcoefficient 3 logExponent (by omega)
      hcore hratio using 1
  norm_num

theorem wireScale_shrink_twentySeven_of_selection
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient)
    (logExponent target : ℕ) (selection : BoundedJumpSelection target) :
    wireScale (coefficient / 27) logExponent target ≤
      wireScale coefficient logExponent selection.core :=
  wireScale_shrink_twentySeven hcoefficient logExponent
    selection.coreAtMostTarget
    (Nat.le_of_lt selection.target_lt_three_core)

theorem nat_le_floor_of_cast_le {value : ℕ} {bound : ℝ}
    (hbound : 0 ≤ bound) (hvalue : (value : ℝ) ≤ bound) :
    value ≤ ⌊bound⌋₊ := by
  exact (Nat.le_floor_iff hbound).2 hvalue

theorem symmetricHardAt_of_wireFamily
    {n size : ℕ} {function : BoolFunction n} {advantage : ℝ}
    (hard :
      AverageHardAt symmetricWireFamily function size advantage)
    (circuit : SymmetricThresholdCircuit n)
    (hwires : circuit.wireCount ≤ size) :
    agreement circuit.eval function ≤ 1 / 2 + advantage :=
  hard circuit.eval ⟨circuit, hwires, rfl⟩

theorem thresholdHardAt_of_wireFamily
    {n size : ℕ} {function : BoolFunction n} {advantage : ℝ}
    (hard :
      AverageHardAt thresholdWireFamily function size advantage)
    (circuit : ThresholdThresholdCircuit n)
    (hwires : circuit.wireCount ≤ size) :
    agreement circuit.eval function ≤ 1 / 2 + advantage :=
  hard circuit.eval ⟨circuit, hwires, rfl⟩

/-- A real-valued headline cap can be consumed by the corresponding natural
family size via the canonical natural floor. -/
theorem symmetricHardAt_of_real_cap
    {n : ℕ} {function : BoolFunction n} {advantage cap : ℝ}
    (hcap : 0 ≤ cap)
    (hard : AverageHardAt symmetricWireFamily function ⌊cap⌋₊ advantage)
    (circuit : SymmetricThresholdCircuit n)
    (hwires : (circuit.wireCount : ℝ) ≤ cap) :
    agreement circuit.eval function ≤ 1 / 2 + advantage :=
  symmetricHardAt_of_wireFamily hard circuit
    (nat_le_floor_of_cast_le hcap hwires)

theorem thresholdHardAt_of_real_cap
    {n : ℕ} {function : BoolFunction n} {advantage cap : ℝ}
    (hcap : 0 ≤ cap)
    (hard : AverageHardAt thresholdWireFamily function ⌊cap⌋₊ advantage)
    (circuit : ThresholdThresholdCircuit n)
    (hwires : (circuit.wireCount : ℝ) ≤ cap) :
    agreement circuit.eval function ≤ 1 / 2 + advantage :=
  thresholdHardAt_of_wireFamily hard circuit
    (nat_le_floor_of_cast_le hcap hwires)

/-- Restricting a target circuit to the scheduled core consumes the factor-27
coefficient shrink and preserves the core advantage exactly. -/
theorem symmetricHard_padSelection
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient)
    (logExponent target : ℕ) (selection : BoundedJumpSelection target)
    {function : BoolFunction selection.core} {advantage : ℝ}
    (hard : AverageHardAt symmetricWireFamily function
      ⌊wireScale coefficient logExponent selection.core⌋₊ advantage)
    (circuit : SymmetricThresholdCircuit target)
    (hwires : (circuit.wireCount : ℝ) ≤
      wireScale (coefficient / 27) logExponent target) :
    agreement circuit.eval
        (padCore function selection.coreAtMostTarget) ≤
      1 / 2 + advantage := by
  have hpadded :
      AverageHardAt symmetricWireFamily
    (padCore function selection.coreAtMostTarget)
        ⌊wireScale coefficient logExponent selection.core⌋₊ advantage :=
    averageHard_padCore
      (family := symmetricWireFamily)
      (core := selection.core) (target := target)
      (size := ⌊wireScale coefficient logExponent selection.core⌋₊)
      symmetricWireFamily_restrictionClosed
      hard selection.coreAtMostTarget
  have hcoreCap :
      0 ≤ wireScale coefficient logExponent selection.core := by
    unfold wireScale
    positivity
  apply symmetricHardAt_of_real_cap hcoreCap hpadded circuit
  exact hwires.trans
    (wireScale_shrink_twentySeven_of_selection
      hcoefficient logExponent target selection)

theorem thresholdHard_padSelection
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient)
    (logExponent target : ℕ) (selection : BoundedJumpSelection target)
    {function : BoolFunction selection.core} {advantage : ℝ}
    (hard : AverageHardAt thresholdWireFamily function
      ⌊wireScale coefficient logExponent selection.core⌋₊ advantage)
    (circuit : ThresholdThresholdCircuit target)
    (hwires : (circuit.wireCount : ℝ) ≤
      wireScale (coefficient / 27) logExponent target) :
    agreement circuit.eval
        (padCore function selection.coreAtMostTarget) ≤
      1 / 2 + advantage := by
  have hpadded :
      AverageHardAt thresholdWireFamily
    (padCore function selection.coreAtMostTarget)
        ⌊wireScale coefficient logExponent selection.core⌋₊ advantage :=
    averageHard_padCore
      (family := thresholdWireFamily)
      (core := selection.core) (target := target)
      (size := ⌊wireScale coefficient logExponent selection.core⌋₊)
      thresholdWireFamily_restrictionClosed
      hard selection.coreAtMostTarget
  have hcoreCap :
      0 ≤ wireScale coefficient logExponent selection.core := by
    unfold wireScale
    positivity
  apply thresholdHardAt_of_real_cap hcoreCap hpadded circuit
  exact hwires.trans
    (wireScale_shrink_twentySeven_of_selection
      hcoefficient logExponent target selection)

end NearCubicWires.WireScaleTransfer
