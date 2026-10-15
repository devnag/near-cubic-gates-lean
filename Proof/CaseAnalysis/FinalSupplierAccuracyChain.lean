import Proof.CaseAnalysis.FinalSupplierWidth
import Proof.CaseAnalysis.FinalFamilyMass

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain

open NearCubicWires
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Section 1 The two witnesses, at the consumer's own field types -/

/-- **`S.failure`.**  The supplier's per-call point error under S-W's uniform
denominator: the rows' requested reciprocal accuracy `1 / (target q + 1)` plus
one ulp of the floor division. -/
noncomputable def failureOf (target arity scale : ℕ → ℕ) :
    (n : ℕ) → BitInput n → List Bool →
      RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → ℝ :=
  fun n _ _ _ =>
    (1 : ℝ) / ((target (arity n) + 1 : ℕ) : ℝ)
      + 1 / ((C10SupplierWidth.denominator (arity n) (scale n) : ℕ) : ℝ)

noncomputable def massOf (limits : ℕ → CanonicalWitnessCodec.LegalSumLimits) :
    (n : ℕ) → BitInput n → List Bool →
      RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → ℝ :=
  fun n _ _ ph => C10FamilyMass.massBound (limits n) ph

/-- **`StageBlock.hfailure`.** -/
theorem failureOf_nonneg (target arity scale : ℕ → ℕ) (n : ℕ) (x : BitInput n)
    (bits : List Bool)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) :
    0 ≤ failureOf target arity scale n x bits ph := by
  simp only [failureOf]
  positivity

/-! ## Section 2 `hpoint` from the row supplier, through the floor division -/

/-- The floor-division supplier answers every AND-four call within the rows' own
failure plus one ulp.  Generic in `rows`, so the THR twin is the same theorem. -/
theorem rowRatio_error_le {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (target arity scale : ℕ)
    (factors : List (Circuit arity))
    (hrows : rows.failure ⟨arity, factors⟩ ≤ (1 : ℝ) / ((target + 1 : ℕ) : ℝ)) :
    |(((C10SupplierWidth.answer rows arity scale factors : ℚ)
          / (C10SupplierWidth.denominator arity scale : ℚ) : ℚ) : ℝ)
        - conjunctionProbability evaluate factors|
      ≤ (1 : ℝ) / ((target + 1 : ℕ) : ℝ)
        + 1 / ((C10SupplierWidth.denominator arity scale : ℕ) : ℝ) := by
  have herr := C10SupplierWidth.answer_div_denominator_error rows arity scale factors
  have hpt := rowSupplier_error_le rows arity factors
  have hcast : |(((C10SupplierWidth.answer rows arity scale factors : ℚ)
            / (C10SupplierWidth.denominator arity scale : ℚ) : ℚ) : ℝ)
        - ((rowSupplier rows arity factors : ℚ) : ℝ)|
      ≤ 1 / ((C10SupplierWidth.denominator arity scale : ℕ) : ℝ) := by
    have hR := (Rat.cast_le (K := ℝ)).mpr herr
    push_cast at hR ⊢
    exact hR
  calc |(((C10SupplierWidth.answer rows arity scale factors : ℚ)
            / (C10SupplierWidth.denominator arity scale : ℚ) : ℚ) : ℝ)
          - conjunctionProbability evaluate factors|
      ≤ |(((C10SupplierWidth.answer rows arity scale factors : ℚ)
              / (C10SupplierWidth.denominator arity scale : ℚ) : ℚ) : ℝ)
            - ((rowSupplier rows arity factors : ℚ) : ℝ)|
          + |((rowSupplier rows arity factors : ℚ) : ℝ)
            - conjunctionProbability evaluate factors| := abs_sub_le _ _ _
    _ ≤ 1 / ((C10SupplierWidth.denominator arity scale : ℕ) : ℝ)
          + (1 : ℝ) / ((target + 1 : ℕ) : ℝ) :=
        add_le_add hcast (hpt.trans hrows)
    _ = (1 : ℝ) / ((target + 1 : ℕ) : ℝ)
          + 1 / ((C10SupplierWidth.denominator arity scale : ℕ) : ℝ) := by ring

/-- **`StageBlock.hpoint`**, at `supplier := fun factors => (answer factors : ℚ)
/ (denominator : ℚ)` and `failure := failureOf target arity scale`. -/
theorem hpoint_of_rows {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (target arity scale : ℕ → ℕ)
    (n : ℕ) (x : BitInput n) (bits : List Bool)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    (factors : List (Circuit (arity n)))
    (hrows : rows.failure ⟨arity n, factors⟩
      ≤ (1 : ℝ) / ((target (arity n) + 1 : ℕ) : ℝ)) :
    |(((C10SupplierWidth.answer rows (arity n) (scale n) factors : ℚ)
          / (C10SupplierWidth.denominator (arity n) (scale n) : ℚ) : ℚ) : ℝ)
        - conjunctionProbability evaluate factors|
      ≤ failureOf target arity scale n x bits ph := by
  simpa only [failureOf] using
    rowRatio_error_le rows (target (arity n)) (arity n) (scale n) factors hrows

/-- The SYM instance: `symmetricFourfoldRows`' failure IS the requested
reciprocal accuracy, so `hrows` is an equality. -/
theorem hpoint_of_symmetricRows (spectrum : ExpanderSpectrumContract)
    (liveScale : ℕ) (target arity scale : ℕ → ℕ) (n : ℕ) (x : BitInput n)
    (bits : List Bool)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    (factors : List (NormalizedSymmetricThresholdCircuit (arity n))) :
    |(((C10SupplierWidth.answer (symmetricFourfoldRows spectrum liveScale target)
            (arity n) (scale n) factors : ℚ)
          / (C10SupplierWidth.denominator (arity n) (scale n) : ℚ) : ℚ) : ℝ)
        - conjunctionProbability NormalizedSymmetricThresholdCircuit.eval factors|
      ≤ failureOf target arity scale n x bits ph :=
  hpoint_of_rows _ target arity scale n x bits ph factors
    (le_of_eq
      (C10SupplierWidth.symmetric_failure spectrum liveScale target ⟨arity n, factors⟩))

/-- The THR rows carry the same requested reciprocal accuracy. -/
theorem threshold_failure (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract)
    (algorithm : ExecutableInterfaces.ExecutableExactDecompositionAlgorithm)
    (liveScale : ℕ) (target : ℕ → ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (thresholdFourfoldRows spectrum theta algorithm liveScale target).failure request
      = (1 : ℝ) / ((target request.q + 1 : ℕ) : ℝ) := rfl

/-- The THR instance of `hpoint_of_rows`. -/
theorem hpoint_of_thresholdRows (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract)
    (algorithm : ExecutableInterfaces.ExecutableExactDecompositionAlgorithm)
    (liveScale : ℕ) (target arity scale : ℕ → ℕ) (n : ℕ) (x : BitInput n)
    (bits : List Bool)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    (factors : List (NormalizedThresholdThresholdCircuit (arity n))) :
    |(((C10SupplierWidth.answer
            (thresholdFourfoldRows spectrum theta algorithm liveScale target)
            (arity n) (scale n) factors : ℚ)
          / (C10SupplierWidth.denominator (arity n) (scale n) : ℚ) : ℚ) : ℝ)
        - conjunctionProbability NormalizedThresholdThresholdCircuit.eval factors|
      ≤ failureOf target arity scale n x bits ph :=
  hpoint_of_rows _ target arity scale n x bits ph factors
    (le_of_eq
      (threshold_failure spectrum theta algorithm liveScale target ⟨arity n, factors⟩))

/-! ## Section 3 `hmass` at the decoded family -/

theorem hmass_of_family {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    (limits : ℕ → CanonicalWitnessCodec.LegalSumLimits) (n : ℕ)
    {circuit : BooleanCircuit (limits n).expectedArity}
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (family : RepairOrdinary.CloseoutWitness.SumFamily Circuit wires description
      (limits n) (pcpp.systematicBits + pcpp.auxiliaryBits))
    (systematicAtom : Fin pcpp.systematicBits → Circuit (limits n).expectedArity)
    (x : BitInput n) (bits : List Bool) :
    (((RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp
          (RepairOrdinary.CloseoutFinalC10ExactnessFamily.familyCoordinate rfl family)
          systematicAtom).coefficientMass : ℚ) : ℝ)
      ≤ massOf limits n x bits ph := by
  simpa only [massOf] using
    C10FamilyMass.familyCoordinate_coefficientMass_le ph pcpp family systematicAtom

/-! ## Section 4 `haccuracy` — the product bound, and the constraint it forces

The budget is `estimationTolerance constants (zeta constants)` and the failure
has two terms, so each term is allotted half of it.  `accuracyTarget` is the
least reciprocal accuracy that pays one term; the two inequalities of
`haccuracy_of_bounds` say that `target` and the uniform denominator both clear
it. -/

/-- Pure arithmetic: a reciprocal weight times a mass is at most half a budget
as soon as twice the mass fits under the weight's own denominator.  No sign
hypothesis on the mass is needed: at `d = 0` the weight is `0`. -/
theorem recip_mul_le_half {epsilon mass d : ℝ} (hepsilon : 0 < epsilon)
    (hd0 : 0 ≤ d) (hd : 2 * mass ≤ d * epsilon) :
    1 / d * mass ≤ epsilon / 2 := by
  rcases eq_or_lt_of_le hd0 with hzero | hpos
  · rw [← hzero]
    simp only [div_zero, zero_mul]
    linarith
  · have hrewrite : 1 / d * mass = mass / d := by
      rw [div_mul_eq_mul_div, one_mul]
    rw [hrewrite, div_le_iff₀ hpos]
    nlinarith [hd]

noncomputable def accuracyTarget {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) : ℕ :=
  ⌈2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
      / estimationTolerance constants (zeta constants)⌉₊

theorem accuracyTarget_spec {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) (d : ℕ)
    (hd : accuracyTarget constants limits ph ≤ d) :
    2 * ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : ℚ) : ℝ)
      ≤ (d : ℝ) * ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  have hpos : 0 < estimationTolerance constants (zeta constants) :=
    (full_error_budget constants).1
  have hceil : 2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
        / estimationTolerance constants (zeta constants)
      ≤ ((⌈2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
            / estimationTolerance constants (zeta constants)⌉₊ : ℕ) : ℚ) :=
    Nat.le_ceil _
  have hunfold : accuracyTarget constants limits ph
      = ⌈2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
          / estimationTolerance constants (zeta constants)⌉₊ := rfl
  rw [hunfold] at hd
  have hdQ : ((⌈2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
        / estimationTolerance constants (zeta constants)⌉₊ : ℕ) : ℚ) ≤ (d : ℚ) := by
    exact_mod_cast hd
  have hle := hceil.trans hdQ
  rw [div_le_iff₀ hpos] at hle
  have hkey : 2 * C10FamilyMass.siteMassBound limits.coefficientMassCap ph
      ≤ (d : ℚ) * estimationTolerance constants (zeta constants) := by linarith
  exact_mod_cast hkey

/-- The product bound at an abstract phase mass: both error terms cleared. -/
theorem failure_mul_mass_le {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) (t d : ℕ)
    (ht : accuracyTarget constants limits ph ≤ t)
    (hd : accuracyTarget constants limits ph ≤ d) :
    ((1 : ℝ) / ((t + 1 : ℕ) : ℝ) + 1 / ((d : ℕ) : ℝ))
        * ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : ℚ) : ℝ)
      ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
    exact_mod_cast (full_error_budget constants).1
  have hA := accuracyTarget_spec constants limits ph (t + 1) (le_trans ht (Nat.le_succ t))
  have hB := accuracyTarget_spec constants limits ph d hd
  have h1 : (1 : ℝ) / ((t + 1 : ℕ) : ℝ)
        * ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : ℚ) : ℝ)
      ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) / 2 :=
    recip_mul_le_half hpos (by positivity) hA
  have h2 : (1 : ℝ) / ((d : ℕ) : ℝ)
        * ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : ℚ) : ℝ)
      ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) / 2 :=
    recip_mul_le_half hpos (by positivity) hB
  have hsplit : ((1 : ℝ) / ((t + 1 : ℕ) : ℝ) + 1 / ((d : ℕ) : ℝ))
        * ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : ℚ) : ℝ)
      = (1 : ℝ) / ((t + 1 : ℕ) : ℝ)
          * ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : ℚ) : ℝ)
        + (1 : ℝ) / ((d : ℕ) : ℝ)
          * ((C10FamilyMass.siteMassBound limits.coefficientMassCap ph : ℚ) : ℝ) := by
    ring
  rw [hsplit]
  linarith

theorem haccuracy_of_bounds {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : ℕ → CanonicalWitnessCodec.LegalSumLimits)
    (target arity scale : ℕ → ℕ)
    (htarget : ∀ (m : ℕ) (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase),
      accuracyTarget constants (limits m) ph ≤ target (arity m))
    (hscale : ∀ (m : ℕ) (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase),
      accuracyTarget constants (limits m) ph
        ≤ C10SupplierWidth.denominator (arity m) (scale m))
    (n : ℕ) (x : BitInput n) (bits : List Bool)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) :
    failureOf target arity scale n x bits ph * massOf limits n x bits ph
      ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  simp only [failureOf, massOf, C10FamilyMass.massBound]
  exact failure_mul_mass_le constants (limits n) ph (target (arity n))
    (C10SupplierWidth.denominator (arity n) (scale n)) (htarget n ph) (hscale n ph)

/-! ## Section 5 The constraint in closed form, for S0 / S1 / S-W's consumers -/

/-- One number per input length: the max of `accuracyTarget` over the three
phases of `CloseoutRowsOriginalSchedule`. -/
noncomputable def accuracyTargetAll {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits) : ℕ :=
  max
    (max (accuracyTarget constants limits
        RepairOrdinary.CloseoutRowsOriginalSchedule.Phase.penalty)
      (accuracyTarget constants limits
        RepairOrdinary.CloseoutRowsOriginalSchedule.Phase.moment))
    (accuracyTarget constants limits
      RepairOrdinary.CloseoutRowsOriginalSchedule.Phase.clause)

theorem accuracyTarget_le_all {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) :
    accuracyTarget constants limits ph ≤ accuracyTargetAll constants limits := by
  cases ph with
  | penalty => exact le_trans (le_max_left _ _) (le_max_left _ _)
  | moment => exact le_trans (le_max_right _ _) (le_max_left _ _)
  | clause => exact le_max_right _ _

/-- **The `scale` half of the constraint, in closed form.**  `Nat.size` bits of
headroom in `arity + scale` is exactly what makes S-W's uniform denominator
clear the requested accuracy at every phase. -/
theorem accuracyTarget_le_denominator {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) (arity scale : ℕ)
    (hsize : Nat.size (accuracyTargetAll constants limits) ≤ arity + scale) :
    accuracyTarget constants limits ph
      ≤ C10SupplierWidth.denominator arity scale :=
  le_trans (accuracyTarget_le_all constants limits ph)
    (le_of_lt (Nat.size_le.mp hsize))

/-- **What the constraint costs `entryWidth`.**  S-W's third floor
(`entryWidth_floor_answer`, `Proof/CaseAnalysis/FinalSupplierWidth.lean`)
already charges `arity n + scale n + 1` bits, so the accuracy constraint costs
`entryWidth` exactly `Nat.size (accuracyTargetAll …)` bits and nothing more. -/
theorem size_lt_entryWidth {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits)
    (coefficientFloor arity scale : ℕ → ℕ) (n : ℕ)
    (hsize : Nat.size (accuracyTargetAll constants limits) ≤ arity n + scale n) :
    Nat.size (accuracyTargetAll constants limits)
      < C10SupplierWidth.entryWidth coefficientFloor arity scale constants n := by
  have hfloor :=
    C10SupplierWidth.entryWidth_floor_answer coefficientFloor arity scale constants n
  omega

/-- **The constraint is SATISFIABLE, with an explicit canonical witness.**
paper.tex:1405-1408 -- "guessed proof descriptions, term counts, witness length,
coefficient masses, and coefficient-bit bounds are a finite list of fixed
polynomial envelopes once the target advantage exponent is fixed.  They are
frozen before the weak machine" -- freezes `limits` before the machine, so it
does not vary with the input length.  At a frozen `limits` the canonical choice

```
target := fun _ => accuracyTargetAll constants limits
scale  := fun _ => Nat.size (accuracyTargetAll constants limits)
```

pays `haccuracy` at EVERY input length, phase, input and proof string, and costs
`entryWidth` exactly `Nat.size (accuracyTargetAll constants limits)` bits -- a
CONSTANT, so S6's hypothesis 13 (`entryWidth N` inside a poly(N) envelope) is
untouched. -/
theorem haccuracy_at_frozen_limits {source : PointwisePCPPAlgorithm}
    (constants : Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits) (arity : ℕ → ℕ) (n : ℕ)
    (x : BitInput n) (bits : List Bool)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase) :
    failureOf (fun _ => accuracyTargetAll constants limits) arity
          (fun _ => Nat.size (accuracyTargetAll constants limits)) n x bits ph
        * massOf (fun _ => limits) n x bits ph
      ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) :=
  haccuracy_of_bounds constants (fun _ => limits)
    (fun _ => accuracyTargetAll constants limits) arity
    (fun _ => Nat.size (accuracyTargetAll constants limits))
    (fun _ phase => accuracyTarget_le_all constants limits phase)
    (fun m phase =>
      accuracyTarget_le_denominator constants limits phase (arity m)
        (Nat.size (accuracyTargetAll constants limits))
        (Nat.le_add_left _ _))
    n x bits ph

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain
