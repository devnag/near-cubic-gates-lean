import Proof.Foundations.SourceContracts

namespace NearCubicWires

open SourceInterfaces

noncomputable def HeadlineTheorem23 : Prop :=
  ∀ advantageExponent : ℝ, 0 < advantageExponent →
    ∃ language : Language,
    ∃ symmetricCoefficient thresholdCoefficient : ℝ,
      InENP language ∧
      0 < symmetricCoefficient ∧
      0 < thresholdCoefficient ∧
      ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          (circuit.wireCount : ℝ) ≤ wireScale symmetricCoefficient 10 n →
          agreement circuit.eval (language n) <
            1 / 2 + inversePolynomialAdvantage n advantageExponent) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          (circuit.wireCount : ℝ) ≤ wireScale thresholdCoefficient 12 n →
          agreement circuit.eval (language n) <
            1 / 2 + inversePolynomialAdvantage n advantageExponent)

noncomputable def HeadlineTheorem25 : Prop :=
  ∀ fixedAdvantage : ℝ, 0 < fixedAdvantage → fixedAdvantage < 1 / 2 →
    ∃ language : Language,
    ∃ symmetricCoefficient thresholdCoefficient : ℝ,
      InENP language ∧
      0 < symmetricCoefficient ∧
      0 < thresholdCoefficient ∧
      ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          1 / 2 + fixedAdvantage ≤ agreement circuit.eval (language n) →
          wireScale symmetricCoefficient 5 n < circuit.wireCount) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          1 / 2 + fixedAdvantage ≤ agreement circuit.eval (language n) →
          wireScale thresholdCoefficient 9 n < circuit.wireCount)

end NearCubicWires
