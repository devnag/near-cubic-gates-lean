import Proof.Foundations.WireScaleTransfer

/-!
# Common physical hard cores and their padded target facts

The recovery dichotomy must freeze one truth table before the two circuit modes
split.  `PhysicalCommonCore` records that table with separate natural wire
budgets for the two physical families; the only target-length loss is the
factor-27 coefficient shrink from `WireScaleTransfer`.
-/

namespace NearCubicWires.PhysicalHardness

open NearCubicWires
open NearCubicWires.AppendixC
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryPipeline
open NearCubicWires.WireScaleTransfer

structure PhysicalCommonCore
    (symmetricCoefficient thresholdCoefficient : ℝ)
    (symmetricLogExponent thresholdLogExponent arity : ℕ) where
  function : BoolFunction arity
  advantage : ℝ
  symmetricHard :
    AverageHardAt symmetricWireFamily function
      ⌊wireScale symmetricCoefficient symmetricLogExponent arity⌋₊ advantage
  thresholdHard :
    AverageHardAt thresholdWireFamily function
      ⌊wireScale thresholdCoefficient thresholdLogExponent arity⌋₊ advantage

noncomputable def PaddedPhysicalModeHardness
    (advantage symmetricCoefficient thresholdCoefficient : ℝ)
    (symmetricLogExponent thresholdLogExponent : ℕ)
    (mode : Mode) {n : ℕ} (function : BoolFunction n) : Prop :=
  match mode with
  | .symmetric =>
      ∀ circuit : SymmetricThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤
            wireScale (symmetricCoefficient / 27)
              symmetricLogExponent n →
          agreement circuit.eval function ≤ 1 / 2 + advantage
  | .threshold =>
      ∀ circuit : ThresholdThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤
            wireScale (thresholdCoefficient / 27)
              thresholdLogExponent n →
          agreement circuit.eval function ≤ 1 / 2 + advantage

theorem padCommonCore
    {symmetricCoefficient thresholdCoefficient : ℝ}
    (hsymmetric : 0 ≤ symmetricCoefficient)
    (hthreshold : 0 ≤ thresholdCoefficient)
    (symmetricLogExponent thresholdLogExponent target : ℕ)
    (selection : BoundedJumpSelection target)
    (core : PhysicalCommonCore
      symmetricCoefficient thresholdCoefficient
      symmetricLogExponent thresholdLogExponent selection.core) :
    ∀ mode,
      PaddedPhysicalModeHardness core.advantage
        symmetricCoefficient thresholdCoefficient
        symmetricLogExponent thresholdLogExponent mode
        (padCore core.function selection.coreAtMostTarget) := by
  intro mode
  cases mode with
  | symmetric =>
      intro circuit hwires
      exact symmetricHard_padSelection hsymmetric symmetricLogExponent
        target selection core.symmetricHard circuit hwires
  | threshold =>
      intro circuit hwires
      exact thresholdHard_padSelection hthreshold thresholdLogExponent
        target selection core.thresholdHard circuit hwires

theorem shrunkCoefficient_positive {coefficient : ℝ}
    (hcoefficient : 0 < coefficient) :
    0 < coefficient / 27 := by
  positivity

end NearCubicWires.PhysicalHardness
