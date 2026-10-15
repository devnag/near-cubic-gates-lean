import Proof.Circuits.HeadlineClosure
import Proof.Foundations.PhysicalHardness

/-!
# Adapters from physical recovery facts to the exact headline closures

These definitions merely expose the already-paid factor-27 coefficients under
the names expected by `HeadlineClosure`.  They add no recovery premise and do
not alter the language, onset, advantage, or per-mode circuit statements.
-/

namespace NearCubicWires.PhysicalHeadlineAdapters

open NearCubicWires
open NearCubicWires.HeadlineClosure
open NearCubicWires.PhysicalHardness
open NearCubicWires.RecoveryPipeline

def RecoveredPerClassFacts.mapHard
    {source target :
      (mode : AppendixC.Mode) → {n : ℕ} → BoolFunction n → Prop}
    {language : Language} {auditAt : ℕ → Prop}
    (facts : RecoveredPerClassFacts source language auditAt)
    (transfer : ∀ (mode : AppendixC.Mode) {n : ℕ}
      (function : BoolFunction n),
      source mode function → target mode function) :
    RecoveredPerClassFacts target language auditAt where
  inENP := facts.inENP
  eventuallyHard := by
    rcases facts.eventuallyHard with ⟨onset, hard⟩
    exact ⟨onset, fun n hn mode =>
      transfer mode (language n) (hard n hn mode)⟩
  selectedCore := facts.selectedCore
  selectionEventually := facts.selectionEventually
  auditEventually := facts.auditEventually

noncomputable def inversePolynomialRecoveryOfPhysical
    (advantageExponent : ℝ)
    {language : Language}
    (symmetricCoefficient thresholdCoefficient : ℝ)
    (symmetricCoefficientPositive : 0 < symmetricCoefficient)
    (thresholdCoefficientPositive : 0 < thresholdCoefficient)
    {auditAt : ℕ → Prop}
    (facts :
      RecoveredPerClassFacts
        (fun mode {n} target =>
          PaddedPhysicalModeHardness
            (inversePolynomialAdvantage n (advantageExponent + 1))
            symmetricCoefficient thresholdCoefficient 10 12 mode target)
        language auditAt) :
    InversePolynomialRecovery advantageExponent where
  language := language
  symmetricCoefficient := symmetricCoefficient / 27
  thresholdCoefficient := thresholdCoefficient / 27
  symmetricCoefficientPositive :=
    shrunkCoefficient_positive symmetricCoefficientPositive
  thresholdCoefficientPositive :=
    shrunkCoefficient_positive thresholdCoefficientPositive
  auditAt := auditAt
  facts := RecoveredPerClassFacts.mapHard facts (by
    intro mode n target hard
    cases mode <;>
      simpa [InversePolynomialModeHardness,
        PaddedPhysicalModeHardness] using hard)

noncomputable def fixedAdvantageRecoveryOfPhysical
    (fixedAdvantage recoveredAdvantage : ℝ)
    {language : Language}
    (symmetricCoefficient thresholdCoefficient : ℝ)
    (symmetricCoefficientPositive : 0 < symmetricCoefficient)
    (thresholdCoefficientPositive : 0 < thresholdCoefficient)
    (recoveredAdvantageNonnegative : 0 ≤ recoveredAdvantage)
    (recoveredAdvantageReserve : recoveredAdvantage < fixedAdvantage)
    {auditAt : ℕ → Prop}
    (facts :
      RecoveredPerClassFacts
        (fun mode {_n} target =>
          PaddedPhysicalModeHardness recoveredAdvantage
            symmetricCoefficient thresholdCoefficient 5 9 mode target)
        language auditAt) :
    FixedAdvantageRecovery fixedAdvantage where
  language := language
  symmetricCoefficient := symmetricCoefficient / 27
  thresholdCoefficient := thresholdCoefficient / 27
  recoveredAdvantage := recoveredAdvantage
  symmetricCoefficientPositive :=
    shrunkCoefficient_positive symmetricCoefficientPositive
  thresholdCoefficientPositive :=
    shrunkCoefficient_positive thresholdCoefficientPositive
  recoveredAdvantageNonnegative := recoveredAdvantageNonnegative
  recoveredAdvantageReserve := recoveredAdvantageReserve
  auditAt := auditAt
  facts := RecoveredPerClassFacts.mapHard facts (by
    intro mode n target hard
    cases mode <;>
      simpa [FixedAdvantageModeHardness,
        PaddedPhysicalModeHardness] using hard)

end NearCubicWires.PhysicalHeadlineAdapters
