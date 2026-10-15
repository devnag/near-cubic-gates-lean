import Proof.Foundations.PhysicalHardness
import Proof.Foundations.ThresholdDAGCompilation

/-!
# Boolean-hard-core recovery for the two physical threshold families

The recovery dichotomy produces hardness against ordinary Boolean circuits.
This module applies the verified shared-DAG simulations once, for both physical
families, and then reuses the unique factor-27 padding theorem.  The remaining
premises are explicit numeric comparisons between the Boolean size cap and the
two desired physical wire caps; no semantic or headline witness is accepted.
-/

namespace NearCubicWires.PhysicalRecovery

open NearCubicWires
open NearCubicWires.AppendixC
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.PhysicalHardness
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces
open NearCubicWires.ThresholdDAGSimulation
open NearCubicWires.WireScaleTransfer

theorem symmetricAverageHard_of_boolean
    (normalization : ThresholdNormalizationContract)
    (core : HardCore booleanCircuitFamily) (wireCap : ℕ)
    (hsize :
      40 * (core.arity + wireCap + 2) ^ 4 ≤ core.size) :
    AverageHardAt symmetricWireFamily core.function
      wireCap core.advantage := by
  intro candidate hcandidate
  rcases hcandidate with ⟨source, hwires, heval⟩
  rcases simulateSymmetricThresholdCircuit normalization source with
    ⟨circuit, hcircuitEval, hcircuitSize⟩
  apply core.hard candidate
  refine ⟨circuit, ?_, ?_⟩
  · apply hcircuitSize.trans
    apply hsize.trans'
    gcongr
  · exact hcircuitEval.trans heval

theorem thresholdAverageHard_of_boolean
    (normalization : ThresholdNormalizationContract)
    (core : HardCore booleanCircuitFamily) (wireCap : ℕ)
    (hsize :
      50 * (core.arity + wireCap + 2) ^ 4 ≤ core.size) :
    AverageHardAt thresholdWireFamily core.function
      wireCap core.advantage := by
  intro candidate hcandidate
  rcases hcandidate with ⟨source, hwires, heval⟩
  rcases simulateThresholdThresholdCircuit normalization source with
    ⟨circuit, hcircuitEval, hcircuitSize⟩
  apply core.hard candidate
  refine ⟨circuit, ?_, ?_⟩
  · apply hcircuitSize.trans
    apply hsize.trans'
    gcongr
  · exact hcircuitEval.trans heval

/-- Build the one common physical core used by both modes.  The two numeric
premises are exactly the cost of the verified simulations and expose all
constant/exponent losses to the caller. -/
noncomputable def physicalCommonCoreOfBoolean
    (normalization : ThresholdNormalizationContract)
    (core : HardCore booleanCircuitFamily)
    (symmetricCoefficient thresholdCoefficient : ℝ)
    (symmetricLogExponent thresholdLogExponent : ℕ)
    (hsymmetricSize :
      40 * (core.arity +
        ⌊wireScale symmetricCoefficient symmetricLogExponent core.arity⌋₊ +
        2) ^ 4 ≤ core.size)
    (hthresholdSize :
      50 * (core.arity +
        ⌊wireScale thresholdCoefficient thresholdLogExponent core.arity⌋₊ +
        2) ^ 4 ≤ core.size) :
    PhysicalCommonCore symmetricCoefficient thresholdCoefficient
      symmetricLogExponent thresholdLogExponent core.arity where
  function := core.function
  advantage := core.advantage
  symmetricHard :=
    symmetricAverageHard_of_boolean normalization core _ hsymmetricSize
  thresholdHard :=
    thresholdAverageHard_of_boolean normalization core _ hthresholdSize

/-- Case 1 first becomes a two-family common core.  The two physical size
ledgers may differ, but the function and advantage remain those of the one
general-circuit core. -/
noncomputable def commonPhysicalCoreOfBoolean
    (normalization : ThresholdNormalizationContract)
    (core : HardCore booleanCircuitFamily)
    (symmetricSize thresholdSize : ℕ)
    (hsymmetricSize :
      40 * (core.arity + symmetricSize + 2) ^ 4 ≤ core.size)
    (hthresholdSize :
      50 * (core.arity + thresholdSize + 2) ^ 4 ≤ core.size) :
    CommonHardCore symmetricWireFamily thresholdWireFamily where
  arity := core.arity
  function := core.function
  symmetricSize := symmetricSize
  thresholdSize := thresholdSize
  advantage := core.advantage
  symmetricHard :=
    symmetricAverageHard_of_boolean normalization core symmetricSize
      hsymmetricSize
  thresholdHard :=
    thresholdAverageHard_of_boolean normalization core thresholdSize
      hthresholdSize

/-- Restrict the separate common-core ledgers to the exact wireScale floors
used by the headline. -/
noncomputable def physicalCommonCoreOfCommon
    (core : CommonHardCore symmetricWireFamily thresholdWireFamily)
    (symmetricCoefficient thresholdCoefficient : ℝ)
    (symmetricLogExponent thresholdLogExponent : ℕ)
    (hsymmetricCap :
      ⌊wireScale symmetricCoefficient symmetricLogExponent core.arity⌋₊ ≤
        core.symmetricSize)
    (hthresholdCap :
      ⌊wireScale thresholdCoefficient thresholdLogExponent core.arity⌋₊ ≤
        core.thresholdSize) :
    PhysicalCommonCore symmetricCoefficient thresholdCoefficient
      symmetricLogExponent thresholdLogExponent core.arity where
  function := core.function
  advantage := core.advantage
  symmetricHard := by
    intro candidate hcandidate
    apply core.symmetricHard candidate
    rcases hcandidate with ⟨circuit, hsize, heval⟩
    exact ⟨circuit, hsize.trans hsymmetricCap, heval⟩
  thresholdHard := by
    intro candidate hcandidate
    apply core.thresholdHard candidate
    rcases hcandidate with ⟨circuit, hsize, heval⟩
    exact ⟨circuit, hsize.trans hthresholdCap, heval⟩

/-- Ratio-only form of physical padding.  `PaddingHardnessTransfer` exposes
the already derived `target < 3·core` fact rather than the schedule's auxiliary
`next` index, so this theorem consumes exactly that public interface. -/
theorem padPhysicalCommonCore
    {symmetricCoefficient thresholdCoefficient : ℝ}
    (hsymmetricCoefficient : 0 ≤ symmetricCoefficient)
    (hthresholdCoefficient : 0 ≤ thresholdCoefficient)
    (symmetricLogExponent thresholdLogExponent target : ℕ)
    {coreArity : ℕ} (hcore : coreArity ≤ target)
    (hratio : target < 3 * coreArity)
    (core : PhysicalCommonCore
      symmetricCoefficient thresholdCoefficient
      symmetricLogExponent thresholdLogExponent coreArity) :
    ∀ mode,
      PaddedPhysicalModeHardness core.advantage
        symmetricCoefficient thresholdCoefficient
        symmetricLogExponent thresholdLogExponent mode
        (padCore core.function hcore) := by
  intro mode
  cases mode with
  | symmetric =>
      intro circuit hwires
      have hpadded :
          AverageHardAt symmetricWireFamily (padCore core.function hcore)
            ⌊wireScale symmetricCoefficient symmetricLogExponent coreArity⌋₊
            core.advantage :=
        averageHard_padCore
          (family := symmetricWireFamily)
          (core := coreArity) (target := target)
          (size :=
            ⌊wireScale symmetricCoefficient symmetricLogExponent coreArity⌋₊)
          symmetricWireFamily_restrictionClosed core.symmetricHard hcore
      have hcap :
          0 ≤ wireScale symmetricCoefficient symmetricLogExponent coreArity := by
        unfold wireScale
        positivity
      apply symmetricHardAt_of_real_cap hcap hpadded circuit
      exact hwires.trans <|
        wireScale_shrink_twentySeven hsymmetricCoefficient
          symmetricLogExponent hcore (Nat.le_of_lt hratio)
  | threshold =>
      intro circuit hwires
      have hpadded :
          AverageHardAt thresholdWireFamily (padCore core.function hcore)
            ⌊wireScale thresholdCoefficient thresholdLogExponent coreArity⌋₊
            core.advantage :=
        averageHard_padCore
          (family := thresholdWireFamily)
          (core := coreArity) (target := target)
          (size :=
            ⌊wireScale thresholdCoefficient thresholdLogExponent coreArity⌋₊)
          thresholdWireFamily_restrictionClosed core.thresholdHard hcore
      have hcap :
          0 ≤ wireScale thresholdCoefficient thresholdLogExponent coreArity := by
        unfold wireScale
        positivity
      apply thresholdHardAt_of_real_cap hcap hpadded circuit
      exact hwires.trans <|
        wireScale_shrink_twentySeven hthresholdCoefficient
          thresholdLogExponent hcore (Nat.le_of_lt hratio)

/-- Concrete constructor for the recovery pipeline's padding adapter.  A
supplier need prove only the displayed cap sufficiency and advantage reserve
for the hard cores it can emit; the circuit simulation and padding semantics
are fully discharged here. -/
theorem physicalPaddingHardnessTransfer
    (advantage : ℕ → ℝ)
    (symmetricCoefficient thresholdCoefficient : ℝ)
    (symmetricLogExponent thresholdLogExponent : ℕ)
    (hsymmetricCoefficient : 0 ≤ symmetricCoefficient)
    (hthresholdCoefficient : 0 ≤ thresholdCoefficient)
    (hsymmetricCap :
      ∀ (core :
          CommonHardCore symmetricWireFamily thresholdWireFamily)
        (target : ℕ)
        (_hcore : core.arity ≤ target) (_hratio : target < 3 * core.arity),
        ⌊wireScale symmetricCoefficient symmetricLogExponent core.arity⌋₊ ≤
          core.symmetricSize)
    (hthresholdCap :
      ∀ (core :
          CommonHardCore symmetricWireFamily thresholdWireFamily)
        (target : ℕ)
        (_hcore : core.arity ≤ target) (_hratio : target < 3 * core.arity),
        ⌊wireScale thresholdCoefficient thresholdLogExponent core.arity⌋₊ ≤
          core.thresholdSize)
    (hadvantage :
      ∀ (core :
          CommonHardCore symmetricWireFamily thresholdWireFamily)
        (target : ℕ)
        (_hcore : core.arity ≤ target) (_hratio : target < 3 * core.arity),
        core.advantage ≤ advantage target) :
    PaddingHardnessTransfer symmetricWireFamily thresholdWireFamily
      (fun mode {n} target =>
        PaddedPhysicalModeHardness (advantage n)
          symmetricCoefficient thresholdCoefficient
          symmetricLogExponent thresholdLogExponent mode target) := by
  refine ⟨?_⟩
  · intro mode core target hcore hratio
    let physical := physicalCommonCoreOfCommon core
      symmetricCoefficient thresholdCoefficient
      symmetricLogExponent thresholdLogExponent
      (hsymmetricCap core target hcore hratio)
      (hthresholdCap core target hcore hratio)
    have hpadded := padPhysicalCommonCore hsymmetricCoefficient
      hthresholdCoefficient symmetricLogExponent thresholdLogExponent
      target hcore hratio physical mode
    cases mode with
    | symmetric =>
        intro circuit hwires
        exact (hpadded circuit hwires).trans <| by
          gcongr
          exact hadvantage core target hcore hratio
    | threshold =>
        intro circuit hwires
        exact (hpadded circuit hwires).trans <| by
          gcongr
          exact hadvantage core target hcore hratio

end NearCubicWires.PhysicalRecovery
