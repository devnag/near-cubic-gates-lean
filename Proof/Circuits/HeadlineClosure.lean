import Proof.Circuits.Headlines
import Proof.Foundations.RecoveryPipeline
import Proof.Foundations.AsymptoticAdapters

/-!
# Closed-form adapters from recovered per-class facts to the exact headlines

The recovery layer naturally proves a non-strict agreement bound with a
strictly smaller reserved advantage.  This module performs only the final
logical conversions: it combines the two modes at one onset, spends the
inverse-polynomial exponent reserve, and contraposes the fixed-advantage cap.
No source theorem or manuscript-composition premise is introduced here.
-/

namespace NearCubicWires.HeadlineClosure

open AppendixC RecoveryPipeline

noncomputable def InversePolynomialModeHardness
    (advantageExponent symmetricCoefficient thresholdCoefficient : ℝ)
    (mode : Mode) {n : ℕ} (target : BoolFunction n) : Prop :=
  match mode with
  | .symmetric =>
      ∀ circuit : SymmetricThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤
            wireScale symmetricCoefficient 10 n →
          agreement circuit.eval target ≤
            1 / 2 +
              inversePolynomialAdvantage n (advantageExponent + 1)
  | .threshold =>
      ∀ circuit : ThresholdThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤
            wireScale thresholdCoefficient 12 n →
          agreement circuit.eval target ≤
            1 / 2 +
              inversePolynomialAdvantage n (advantageExponent + 1)

structure InversePolynomialRecovery (advantageExponent : ℝ) where
  language : Language
  symmetricCoefficient : ℝ
  thresholdCoefficient : ℝ
  symmetricCoefficientPositive : 0 < symmetricCoefficient
  thresholdCoefficientPositive : 0 < thresholdCoefficient
  auditAt : ℕ → Prop
  facts :
    RecoveredPerClassFacts
      (InversePolynomialModeHardness advantageExponent
        symmetricCoefficient thresholdCoefficient)
      language auditAt

theorem inversePolynomialRecovery_headline
    {advantageExponent : ℝ}
    (recovery : InversePolynomialRecovery advantageExponent) :
    ∃ language : Language,
    ∃ symmetricCoefficient thresholdCoefficient : ℝ,
      InENP language ∧
      0 < symmetricCoefficient ∧
      0 < thresholdCoefficient ∧
      ∃ onset, ∀ n, onset ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          (circuit.wireCount : ℝ) ≤
              wireScale symmetricCoefficient 10 n →
            agreement circuit.eval (language n) <
              1 / 2 +
                inversePolynomialAdvantage n advantageExponent) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          (circuit.wireCount : ℝ) ≤
              wireScale thresholdCoefficient 12 n →
            agreement circuit.eval (language n) <
              1 / 2 +
                inversePolynomialAdvantage n advantageExponent) := by
  rcases recovery.facts.eventuallyHard with ⟨hardnessOnset, hhard⟩
  refine ⟨recovery.language, recovery.symmetricCoefficient,
    recovery.thresholdCoefficient, recovery.facts.inENP,
    recovery.symmetricCoefficientPositive,
    recovery.thresholdCoefficientPositive, max hardnessOnset 2, ?_⟩
  intro n hn
  have hhardnessOnset : hardnessOnset ≤ n :=
    le_trans (le_max_left _ _) hn
  have hnTwo : 2 ≤ n := le_trans (le_max_right _ _) hn
  constructor
  · intro circuit hwires
    apply agreement_lt_of_exponent_reserve hnTwo
    exact hhard n hhardnessOnset .symmetric circuit hwires
  · intro circuit hwires
    apply agreement_lt_of_exponent_reserve hnTwo
    exact hhard n hhardnessOnset .threshold circuit hwires

noncomputable def FixedAdvantageModeHardness
    (recoveredAdvantage symmetricCoefficient thresholdCoefficient : ℝ)
    (mode : Mode) {n : ℕ} (target : BoolFunction n) : Prop :=
  match mode with
  | .symmetric =>
      ∀ circuit : SymmetricThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤
            wireScale symmetricCoefficient 5 n →
          agreement circuit.eval target ≤ 1 / 2 + recoveredAdvantage
  | .threshold =>
      ∀ circuit : ThresholdThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤
            wireScale thresholdCoefficient 9 n →
          agreement circuit.eval target ≤ 1 / 2 + recoveredAdvantage

structure FixedAdvantageRecovery (fixedAdvantage : ℝ) where
  language : Language
  symmetricCoefficient : ℝ
  thresholdCoefficient : ℝ
  recoveredAdvantage : ℝ
  symmetricCoefficientPositive : 0 < symmetricCoefficient
  thresholdCoefficientPositive : 0 < thresholdCoefficient
  recoveredAdvantageNonnegative : 0 ≤ recoveredAdvantage
  recoveredAdvantageReserve : recoveredAdvantage < fixedAdvantage
  auditAt : ℕ → Prop
  facts :
    RecoveredPerClassFacts
      (FixedAdvantageModeHardness recoveredAdvantage
        symmetricCoefficient thresholdCoefficient)
      language auditAt

theorem fixedAdvantageRecovery_headline
    {fixedAdvantage : ℝ}
    (recovery : FixedAdvantageRecovery fixedAdvantage) :
    ∃ language : Language,
    ∃ symmetricCoefficient thresholdCoefficient : ℝ,
      InENP language ∧
      0 < symmetricCoefficient ∧
      0 < thresholdCoefficient ∧
      ∃ onset, ∀ n, onset ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          1 / 2 + fixedAdvantage ≤
              agreement circuit.eval (language n) →
            wireScale symmetricCoefficient 5 n <
              circuit.wireCount) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          1 / 2 + fixedAdvantage ≤
              agreement circuit.eval (language n) →
            wireScale thresholdCoefficient 9 n <
              circuit.wireCount) := by
  rcases recovery.facts.eventuallyHard with ⟨hardnessOnset, hhard⟩
  refine ⟨recovery.language, recovery.symmetricCoefficient,
    recovery.thresholdCoefficient, recovery.facts.inENP,
    recovery.symmetricCoefficientPositive,
    recovery.thresholdCoefficientPositive, hardnessOnset, ?_⟩
  intro n hn
  constructor
  · intro circuit hagreement
    apply strictWireLowerBound_of_capHard circuit.wireCount
      (wireScale recovery.symmetricCoefficient 5 n)
      (agreement circuit.eval (recovery.language n))
      (1 / 2 + fixedAdvantage)
    · intro hwires
      apply agreement_lt_of_fixed_reserve
      · exact hhard n hn .symmetric circuit hwires
      · exact recovery.recoveredAdvantageReserve
    · exact hagreement
  · intro circuit hagreement
    apply strictWireLowerBound_of_capHard circuit.wireCount
      (wireScale recovery.thresholdCoefficient 9 n)
      (agreement circuit.eval (recovery.language n))
      (1 / 2 + fixedAdvantage)
    · intro hwires
      apply agreement_lt_of_fixed_reserve
      · exact hhard n hn .threshold circuit hwires
      · exact recovery.recoveredAdvantageReserve
    · exact hagreement

end NearCubicWires.HeadlineClosure
