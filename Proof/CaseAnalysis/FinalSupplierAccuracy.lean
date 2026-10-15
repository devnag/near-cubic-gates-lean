import Proof.CaseAnalysis.FinalRealizes
import Proof.Supplier.SupplierEstimator

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **The supplier.**  The rows' canonical rational output at arity `arity`. -/
noncomputable def rowSupplier {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) : ℚ :=
  decodeSupplierRational (rows.outputCode ⟨arity, circuits⟩)

/-- The supplier's answer as a COUNT, the shape S1's `Calls` record carries. -/
def rowAnswer {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) : ℕ :=
  (rows.aggregation ⟨arity, circuits⟩).acceptanceCount

/-- The supplier's denominator, which is per-request: `rowCount * 2 ^ arity`. -/
def rowDenominator {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) : ℕ :=
  rows.rowCount ⟨arity, circuits⟩ * 2 ^ arity

/-- **The `hsupplier` bridge S1 needs.**  `count / denominator` IS the
supplier's answer, so a record stream carrying `rowAnswer` over
`rowDenominator` `Calls` this supplier. -/
theorem rowSupplier_eq_ratio {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) :
    ((rowAnswer rows arity circuits : ℚ) /
        (rowDenominator rows arity circuits : ℚ)) =
      rowSupplier rows arity circuits := by
  rw [rowSupplier, FourfoldRowPreprocessor.outputCode,
    FiniteRowAggregation.decode_outputCode]
  rw [rowAnswer, rowDenominator]
  congr 1
  rw [FiniteRowAggregation.sampleCount, Fintype.card_fin, card_bitInput]

/-! ## §2 `hpoint` -/

/-- **The supplier answers every AND-four call within the rows' failure.**
Paper C.10.1: the machine "estimates `mu = E_{i,u} F_i(u)` by expanding it into
AND-four supplier calls"; this is the per-call guarantee for one such call, and
the `u`-average lives entirely inside `conjunctionProbability`. -/
theorem rowSupplier_error_le {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) :
    |((rowSupplier rows arity circuits : ℚ) : ℝ) -
        conjunctionProbability evaluate circuits| ≤
      rows.failure ⟨arity, circuits⟩ := by
  have hdecode := rows.decode_outputCode ⟨arity, circuits⟩
  have haccurate := rows.accurate ⟨arity, circuits⟩
  rw [rowSupplier, hdecode]
  exact haccurate

/-! ## §3 The two production families, at the failure the paper names

`symmetricFourfoldRows` is `thm:supplier-fixed`'s row family (paper.tex:721,
carried exponent 5) and `thresholdFourfoldRows` is `thm:supplier-inverse`'s
(paper.tex:701, exponent 9).  Both read their failure straight off the
requested reciprocal accuracy. -/

/-- The symmetric rows' failure at a constant requested accuracy. -/
theorem symmetricFourfoldRows_failure (spectrum : ExpanderSpectrumContract)
    (liveScale target arity : ℕ)
    (circuits : List (NormalizedSymmetricThresholdCircuit arity)) :
    (symmetricFourfoldRows spectrum liveScale fun _ => target).failure
        ⟨arity, circuits⟩ = (1 : ℝ) / ((target + 1 : ℕ) : ℝ) :=
  rfl

/-- The threshold rows' failure at a constant requested accuracy. -/
theorem thresholdFourfoldRows_failure (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract)
    (algorithm : ExecutableInterfaces.ExecutableExactDecompositionAlgorithm)
    (liveScale target arity : ℕ)
    (circuits : List (NormalizedThresholdThresholdCircuit arity)) :
    (thresholdFourfoldRows spectrum theta algorithm liveScale
        fun _ => target).failure ⟨arity, circuits⟩ =
      (1 : ℝ) / ((target + 1 : ℕ) : ℝ) :=
  rfl

/-- **SYM supplier accuracy.**  Paper `thm:supplier-fixed`: "estimates the
conjunction probability of at most four normalized `q`-input SYMTHR circuits to
additive error at most `epsilon`". -/
theorem symmetricSupplier_error_le (spectrum : ExpanderSpectrumContract)
    (liveScale target arity : ℕ)
    (circuits : List (NormalizedSymmetricThresholdCircuit arity)) :
    |((rowSupplier (symmetricFourfoldRows spectrum liveScale fun _ => target)
            arity circuits : ℚ) : ℝ) -
        conjunctionProbability NormalizedSymmetricThresholdCircuit.eval
          circuits| ≤ (1 : ℝ) / ((target + 1 : ℕ) : ℝ) :=
  rowSupplier_error_le _ arity circuits

/-- **THR supplier accuracy.**  Paper `thm:supplier-inverse`: "estimates their
conjunction probability to error at most `q^{-D}`". -/
theorem thresholdSupplier_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract)
    (algorithm : ExecutableInterfaces.ExecutableExactDecompositionAlgorithm)
    (liveScale target arity : ℕ)
    (circuits : List (NormalizedThresholdThresholdCircuit arity)) :
    |((rowSupplier (thresholdFourfoldRows spectrum theta algorithm liveScale
            fun _ => target) arity circuits : ℚ) : ℝ) -
        conjunctionProbability NormalizedThresholdThresholdCircuit.eval
          circuits| ≤ (1 : ℝ) / ((target + 1 : ℕ) : ℝ) :=
  rowSupplier_error_le _ arity circuits

/-! ## §4 `hbudget` -/

/-- The phase coefficient-mass ledger is nonnegative. -/
theorem phaseMassCap_nonneg (ph : CloseoutRowsOriginalSchedule.Phase)
    (mass : ℚ) (hmass : 0 ≤ mass) : 0 ≤ phaseMassCap ph mass := by
  cases ph <;>
    simp only [phaseMassCap, coordinateMassCap] <;>
    nlinarith [sq_nonneg mass, sq_nonneg (1 + mass), pow_nonneg hmass 3,
      pow_nonneg hmass 4]

/-- **The requested supplier accuracy, read off the paper's own two
quantities.**  `phaseMassCap ph mass` is the coefficient mass
(paper.tex:1411's `q^{rho_coef}`, the `(1+Lambda)^4` factor of
paper.tex:1371) and `estimationTolerance constants (zeta constants)` is
`eps_est` (paper C.10.2).  The requested reciprocal accuracy is their ratio,
rounded up.  Nothing else is chosen. -/
noncomputable def toleranceDenominator {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (ph : CloseoutRowsOriginalSchedule.Phase)
    (mass : ℚ) : ℕ :=
  ⌈phaseMassCap ph mass / estimationTolerance constants (zeta constants)⌉₊

/-- **THE BUDGET (paper C.10.2).**  At the requested accuracy, the propagated
estimation error `failure * mass` is below `eps_est`.  This is exactly
`Realizes.hbudget`. -/
theorem toleranceDenominator_budget {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (ph : CloseoutRowsOriginalSchedule.Phase)
    (mass : ℚ) (hmass : 0 ≤ mass) :
    (1 : ℝ) / ((toleranceDenominator constants ph mass + 1 : ℕ) : ℝ) *
        ((phaseMassCap ph mass : ℚ) : ℝ) ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  have hpos : 0 < estimationTolerance constants (zeta constants) :=
    (full_error_budget constants).1
  have hM : 0 ≤ phaseMassCap ph mass := phaseMassCap_nonneg ph mass hmass
  have hceil :
      phaseMassCap ph mass / estimationTolerance constants (zeta constants) ≤
        ((toleranceDenominator constants ph mass : ℕ) : ℚ) :=
    Nat.le_ceil _
  have hnum : phaseMassCap ph mass ≤
      ((toleranceDenominator constants ph mass : ℕ) : ℚ) *
        estimationTolerance constants (zeta constants) :=
    (div_le_iff₀ hpos).1 hceil
  have hnumR :
      ((phaseMassCap ph mass : ℚ) : ℝ) ≤
        ((toleranceDenominator constants ph mass : ℕ) : ℝ) *
          ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
    exact_mod_cast hnum
  have hposR :
      (0 : ℝ) < ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
    exact_mod_cast hpos
  have hMR : (0 : ℝ) ≤ ((phaseMassCap ph mass : ℚ) : ℝ) := by exact_mod_cast hM
  have hden :
      (0 : ℝ) < ((toleranceDenominator constants ph mass + 1 : ℕ) : ℝ) := by
    push_cast
    positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
  push_cast
  nlinarith [hnumR, hposR, hMR]

/-! ## §5 The fused deliverable: `Realizes` with both supplier fields closed -/

noncomputable def realizes_of_rowSupplier {t s : ℕ} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm}
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (ph : CloseoutRowsOriginalSchedule.Phase) (constants : Constants source)
    (pcpp : PointwisePCPP circuit)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial (Circuit n) 1)
    (hcoordinate :
      CoordinateExpands pcpp (evaluate (q := n)) proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Circuit n)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (mass : ℚ) (hmassNonneg : 0 ≤ mass)
    (hmass : ∀ j, (coordinate j).coefficientMass ≤ mass)
    (hrows : ∀ circuits : List (Circuit n),
      rows.failure ⟨n, circuits⟩ ≤
        (1 : ℝ) / ((toleranceDenominator constants ph mass + 1 : ℕ) : ℝ))
    (p : Machine t s) (budget : ℕ) (hin : Fin t → ℕ) (tin : Fin t → List Bool)
    (port : Fin t) (width : ℕ)
    (heads : Fin t → ℕ) (exit : Fin t → List Bool)
    (run : Step p budget hin tin heads exit)
    (result : CompetitorValidity.Estimate) (hvalid : result.Valid width)
    (hencoded : exit port =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord width result 1 1)
    (hvaluesum : ((result.value : ℚ) : ℝ) =
      (phasePolynomial ph pcpp coordinate systematicAtom).estimatedMean
        (rowSupplier rows n)) :
    Realizes ph constants pcpp proofValue (evaluate (q := n)) p budget hin tin
      port width :=
  realizes_of_phasePolynomial ph constants pcpp (evaluate (q := n)) proofValue
    coordinate hcoordinate systematicAtom hsystematic (rowSupplier rows n)
    ((1 : ℝ) / ((toleranceDenominator constants ph mass + 1 : ℕ) : ℝ))
    (by positivity)
    (fun circuits =>
      le_trans (rowSupplier_error_le rows n circuits) (hrows circuits))
    ((phaseMassCap ph mass : ℚ) : ℝ)
    (by
      exact_mod_cast phasePolynomial_coefficientMass_le ph pcpp coordinate
        systematicAtom mass hmassNonneg hmass)
    (toleranceDenominator_budget constants ph mass hmassNonneg)
    p budget hin tin port width heads exit run result hvalid hencoded hvaluesum

/-- The SYM instance of the `hrows` hypothesis: an EQUALITY, so the symmetric
rows request exactly the accuracy the budget needs.  This is the clean
replacement for the prohibited `estimator_symmetricRows_failure_le`. -/
theorem symmetricRows_failure_le {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (ph : CloseoutRowsOriginalSchedule.Phase)
    (mass : ℚ) (spectrum : ExpanderSpectrumContract) (liveScale n : ℕ)
    (circuits : List (NormalizedSymmetricThresholdCircuit n)) :
    (symmetricFourfoldRows spectrum liveScale fun _ =>
          toleranceDenominator constants ph mass).failure ⟨n, circuits⟩ ≤
      (1 : ℝ) / ((toleranceDenominator constants ph mass + 1 : ℕ) : ℝ) :=
  le_of_eq rfl

/-- The THR instance of the same, replacing
`estimator_thresholdRows_failure_le`. -/
theorem thresholdRows_failure_le {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (ph : CloseoutRowsOriginalSchedule.Phase)
    (mass : ℚ) (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract)
    (algorithm : ExecutableInterfaces.ExecutableExactDecompositionAlgorithm)
    (liveScale n : ℕ)
    (circuits : List (NormalizedThresholdThresholdCircuit n)) :
    (thresholdFourfoldRows spectrum theta algorithm liveScale fun _ =>
          toleranceDenominator constants ph mass).failure ⟨n, circuits⟩ ≤
      (1 : ℝ) / ((toleranceDenominator constants ph mass + 1 : ℕ) : ℝ) :=
  le_of_eq rfl

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
