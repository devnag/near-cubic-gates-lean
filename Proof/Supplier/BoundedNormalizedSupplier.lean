import Proof.Circuits.ComponentwisePolynomial
import Proof.Foundations.SupplierPipeline

/-!
# Supplier guarantees on normalization-produced circuits

The threshold-normalization source returns explicit parameter bounds.  Those
bounds are essential: a wire cap controls support incidence, but cannot bound
the exact-decomposition output of an arbitrarily large coefficient encoding.
This module records the single admissible supplier interface used by recovery;
it reuses the same estimator algorithms and only adds the normalization
certificate at the existing guarantee boundary.
-/

namespace NearCubicWires.BoundedNormalizedSupplier

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

def SymmetricNormalizationBounded {q : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit q) : Prop :=
  ∀ index,
    (circuit.bottom index).gate.parametersBoundedBy (q ^ q)

def ThresholdNormalizationBounded {q : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit q) : Prop :=
  (∀ index,
      (circuit.bottom index).gate.parametersBoundedBy (q ^ q)) ∧
    circuit.top.gate.parametersBoundedBy
      (circuit.bottomCount ^ circuit.bottomCount)

/-- The canonical supplier guarantee.  Eligibility follows the wire cap so
the source-facing quantifier order remains unchanged apart from the necessary
normalization certificate. -/
def MeetsFourfoldSupplierGuaranteeOn
    {Circuit : CircuitFamily}
    (eligible : {q : ℕ} → Circuit q → Prop)
    (evaluate : {q : ℕ} → Circuit q → BitInput q → Bool)
    (wires description : {q : ℕ} → Circuit q → ℕ)
    (encodeCircuit : {q : ℕ} → Circuit q → ℕ)
    (algorithm :
      ExecutableFourfoldEstimator Circuit encodeCircuit description)
    (accuracy : ℕ → ℝ)
    (capCoefficient runtimeCoefficient : ℝ)
    (capLogExponent runtimeDegree onset : ℕ)
    (savingExponent : ℝ) : Prop :=
  ∀ q : ℕ, onset ≤ q → 0 < q →
    ∀ circuits : List (Circuit q), circuits.length ≤ 4 →
      (∀ circuit ∈ circuits,
        (wires circuit : ℝ) ≤
          wireScale capCoefficient capLogExponent q) →
      (∀ circuit ∈ circuits, eligible circuit) →
      |(algorithm.estimate circuits : ℝ) -
          conjunctionProbability evaluate circuits| ≤ accuracy q ∧
        (algorithm.steps circuits : ℝ) ≤
          supplierRuntimeEnvelope runtimeCoefficient runtimeDegree
            savingExponent q (batchDescription description circuits) ∧
        (algorithm.registerBits circuits : ℝ) ≤
          supplierRegisterEnvelope runtimeCoefficient runtimeDegree q
            (batchDescription description circuits)

/-- Bounded form of Theorem A.1/S.1 used after support-preserving
normalization. -/
noncomputable def InversePolynomialFourfoldSupplier : Prop :=
  ∀ accuracyExponent savingExponent : ℝ,
    0 < accuracyExponent → 0 < savingExponent →
    ∃ symmetricCap thresholdCap : ℝ,
    ∃ symmetricRuntime thresholdRuntime : ℝ,
    ∃ symmetricDegree thresholdDegree onset : ℕ,
    ∃ symmetricAlgorithm :
      ExecutableFourfoldEstimator NormalizedSymmetricThresholdCircuit
        encodeNormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.descriptionBits,
    ∃ thresholdAlgorithm :
      ExecutableFourfoldEstimator NormalizedThresholdThresholdCircuit
        encodeNormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.descriptionBits,
      0 < symmetricCap ∧ 0 < thresholdCap ∧
      0 < symmetricRuntime ∧ 0 < thresholdRuntime ∧
      MeetsFourfoldSupplierGuaranteeOn
        SymmetricNormalizationBounded
        NormalizedSymmetricThresholdCircuit.eval
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits
        encodeNormalizedSymmetricThresholdCircuit
        symmetricAlgorithm
        (fun q => inversePolynomialAdvantage q accuracyExponent)
        symmetricCap symmetricRuntime 7 symmetricDegree onset
        savingExponent ∧
      MeetsFourfoldSupplierGuaranteeOn
        ThresholdNormalizationBounded
        NormalizedThresholdThresholdCircuit.eval
        NormalizedThresholdThresholdCircuit.wireCount
        NormalizedThresholdThresholdCircuit.descriptionBits
        encodeNormalizedThresholdThresholdCircuit
        thresholdAlgorithm
        (fun q => inversePolynomialAdvantage q accuracyExponent)
        thresholdCap thresholdRuntime 9 thresholdDegree onset
        savingExponent

/-- Bounded fixed-accuracy symmetric supplier A.2/S.2. -/
noncomputable def FixedAccuracySymmetricSupplier : Prop :=
  ∀ epsilon savingExponent : ℝ,
    0 < epsilon → epsilon < 1 / 2 → 0 < savingExponent →
    ∃ capCoefficient runtimeCoefficient : ℝ,
    ∃ runtimeDegree onset : ℕ,
    ∃ algorithm :
      ExecutableFourfoldEstimator NormalizedSymmetricThresholdCircuit
        encodeNormalizedSymmetricThresholdCircuit
        NormalizedSymmetricThresholdCircuit.descriptionBits,
      0 < capCoefficient ∧ 0 < runtimeCoefficient ∧
      MeetsFourfoldSupplierGuaranteeOn
        SymmetricNormalizationBounded
        NormalizedSymmetricThresholdCircuit.eval
        NormalizedSymmetricThresholdCircuit.wireCount
        NormalizedSymmetricThresholdCircuit.descriptionBits
        encodeNormalizedSymmetricThresholdCircuit
        algorithm (fun _ => epsilon)
        capCoefficient runtimeCoefficient 5 runtimeDegree onset
        savingExponent

end NearCubicWires.BoundedNormalizedSupplier

namespace NearCubicWires.ComponentwisePolynomial

open NearCubicWires
open NearCubicWires.BoundedNormalizedSupplier
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SupplierPipeline

/-- A componentwise degree-four polynomial inherits the canonical supplier
error bound once every factor carries both the wire and normalization
certificates required by the executable supplier. -/
theorem estimatedMean_error_le_of_fourfoldGuaranteeOn
    {Circuit : SupplierPipeline.CircuitFamily}
    (eligible : {q : ℕ} → Circuit q → Prop)
    (evaluate : {q : ℕ} → Circuit q → BitInput q → Bool)
    (wires description : {q : ℕ} → Circuit q → ℕ)
    (encodeCircuit : {q : ℕ} → Circuit q → ℕ)
    (algorithm :
      ExecutableFourfoldEstimator Circuit encodeCircuit description)
    (accuracy : ℕ → ℝ)
    (capCoefficient runtimeCoefficient : ℝ)
    (capLogExponent runtimeDegree onset : ℕ)
    (savingExponent : ℝ)
    (guarantee :
      MeetsFourfoldSupplierGuaranteeOn eligible evaluate wires description
        encodeCircuit algorithm accuracy capCoefficient runtimeCoefficient
        capLogExponent runtimeDegree onset savingExponent)
    {degree q : ℕ} (hdegree : degree ≤ 4)
    (hqOnset : onset ≤ q) (hqPositive : 0 < q)
    (polynomial : CircuitPolynomial (Circuit q) degree)
    (hwires : polynomial.FactorsSatisfy fun circuit =>
      (wires circuit : ℝ) ≤
        wireScale capCoefficient capLogExponent q)
    (heligible : polynomial.FactorsSatisfy eligible) :
    |polynomial.estimatedMean algorithm.estimate -
        polynomial.exactMean (evaluate (q := q))| ≤
      accuracy q * (polynomial.coefficientMass : ℝ) := by
  apply estimatedMean_error_le
  intro monomial hmonomial
  exact
    (guarantee q hqOnset hqPositive monomial.factors
      (monomial.degree_le.trans hdegree)
      (hwires monomial hmonomial)
      (heligible monomial hmonomial)).1

end NearCubicWires.ComponentwisePolynomial
