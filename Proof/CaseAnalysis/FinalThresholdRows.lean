import Proof.CaseAnalysis.FinalSources
import Proof.CaseAnalysis.FinalSupplierAccuracy

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalk

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable section

/-! ## §1 The disjoint child sum, as a Boolean disjunction

Paper A.12 / `thm:supplier-inverse`: the exact decomposition of a normalized
threshold top into disjoint children makes the fourfold conjunction the
DISJOINT SUM over child tuples.  `ThresholdRows.selection_sum` is that sum at
the corrected source; here it is turned into the Boolean aggregation the row
compiler actually emits. -/

/-- The exact (pre-prime, pre-list) row of one child tuple. -/
def exactRow (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) (input : BitInput r.q) : Bool :=
  decide ((ThresholdRows.equation a r sel).Holds
    (fun index => ((thresholdFourfoldOccurrences r).get index).eval input))

theorem exactRow_toNat (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) (input : BitInput r.q) :
    (exactRow a r sel input).toNat =
      (if (ThresholdRows.equation a r sel).Holds
        (fun index => ((thresholdFourfoldOccurrences r).get index).eval input)
        then 1 else 0) := by
  unfold exactRow
  by_cases hholds : (ThresholdRows.equation a r sel).Holds
      (fun index => ((thresholdFourfoldOccurrences r).get index).eval input)
  · rw [if_pos hholds, decide_eq_true hholds]
    rfl
  · rw [if_neg hholds, decide_eq_false hholds]
    rfl

/-- **The disjoint child sum (paper A.12).**  Exactly one child tuple accepts
per accepting input, so the tuple rows SUM to the fourfold conjunction. -/
theorem exactRow_sum (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (input : BitInput r.q) :
    (∑ sel : ThresholdRows.Selection a r, (exactRow a r sel input).toNat) =
      (conjunctionBit NormalizedThresholdThresholdCircuit.eval
        r.circuits input).toNat := by
  rw [← ThresholdRows.selection_sum a r input]
  exact Finset.sum_congr rfl (fun sel _ => exactRow_toNat a r sel input)

/-- Disjointness makes Boolean DISJUNCTION the correct tuple aggregation. -/
theorem exactDisjunction_eq_conjunction (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (input : BitInput r.q) :
    finiteBoolDisjunction
        (fun sel : ThresholdRows.Selection a r => exactRow a r sel input) =
      conjunctionBit NormalizedThresholdThresholdCircuit.eval
        r.circuits input := by
  have hsum := exactRow_sum a r input
  apply Bool.eq_iff_iff.mpr
  rw [finiteBoolDisjunction_eq_true_iff]
  constructor
  · rintro ⟨sel, hsel⟩
    have hpositive :
        0 < ∑ candidate : ThresholdRows.Selection a r,
          (exactRow a r candidate input).toNat := by
      rw [Finset.sum_pos_iff]
      exact ⟨sel, Finset.mem_univ sel, by simp [hsel]⟩
    cases htarget :
        conjunctionBit NormalizedThresholdThresholdCircuit.eval
          r.circuits input
    · exfalso
      have hzero :
          (∑ candidate : ThresholdRows.Selection a r,
            (exactRow a r candidate input).toNat) = 0 := by
        simpa [htarget] using hsum
      exact (Nat.not_lt_zero _ (hzero ▸ hpositive))
    · rfl
  · intro htarget
    have hpositive :
        0 < ∑ sel : ThresholdRows.Selection a r,
          (exactRow a r sel input).toNat := by
      rw [hsum, htarget]
      decide
    rcases Finset.sum_pos_iff.mp hpositive with ⟨sel, _, hsel⟩
    refine ⟨sel, ?_⟩
    cases hvalue : exactRow a r sel input
    · simp [hvalue] at hsel
    · rfl

/-- The concrete tuple/prime/list row at the corrected source. -/
def selectionRow (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) : Bool :=
  canonicalOccurrenceCoefficientRadixRow
    (digits := modulusDigitCount prime.val)
    (thresholdFourfoldOccurrences r) liveScale denominator input
    Finset.univ
    (modularCoefficientResidue (ThresholdRows.equation a r sel) prime.val)
    sample prime.val
    (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
      (ThresholdRows.equation a r sel) prime.val)

/-- **List error for one tuple (paper A.5/A.9 item 4).** -/
theorem selectionRow_mismatch_reciprocal (spectrum : ExpanderSpectrumContract)
    (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ}
    (prime : PrimeIndex cutoff) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            (thresholdFourfoldOccurrences r) liveScale denominator =>
          selectionRow a r liveScale denominator input sel prime sample !=
            modularEquationHolds (ThresholdRows.equation a r sel) prime
              (fun index =>
                ((thresholdFourfoldOccurrences r).get index).eval input)) ≤
      (modulusDigitCount prime.val : ℝ) / (denominator + 1 : ℕ) := by
  have hprimePositive : 0 < prime.val :=
    (mem_primesUpTo.mp prime.property).1.pos
  have hbound :=
    canonicalOccurrenceCoefficientRadixRow_mismatch_reciprocal spectrum
      (thresholdFourfoldOccurrences r) liveScale denominator input
      Finset.univ
      (modularCoefficientResidue (ThresholdRows.equation a r sel) prime.val)
      prime.val
      (modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
        (ThresholdRows.equation a r sel) prime.val)
      (fun index =>
        modularCoefficientResidue_lt (ThresholdRows.equation a r sel)
          prime.val hprimePositive index)
  have htarget :
      decide
          ((modularResidualOffset (thresholdFourfoldOccurrences r) liveScale
                input (ThresholdRows.equation a r sel) prime.val +
              ∑ index ∈
                  (Finset.univ :
                    Finset (Fin (thresholdFourfoldOccurrences r).length)),
                modularCoefficientResidue (ThresholdRows.equation a r sel)
                    prime.val index *
                  (occurrenceResidualVariable (thresholdFourfoldOccurrences r)
                    (normalizedLiveSet (thresholdFourfoldOccurrences r)
                      liveScale)
                    input index).toNat) %
            prime.val = 0) =
        modularEquationHolds (ThresholdRows.equation a r sel) prime
          (fun index =>
            ((thresholdFourfoldOccurrences r).get index).eval input) := by
    apply Bool.eq_iff_iff.mpr
    unfold modularEquationHolds
    simp only [decide_eq_true_eq]
    exact modularResidualEquation_spec (thresholdFourfoldOccurrences r)
      liveScale input (ThresholdRows.equation a r sel) prime.val
      hprimePositive
  simpa [selectionRow, htarget, modulusDigitCount] using hbound

/-! ## §3 One prime's row: the disjoint tuples share a prime and a seed -/

/-- All child tuples share one prime and one amplified-list seed; the
aggregation is disjunction because the child decomposition is disjoint. -/
def primeRow (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput r.q)
    {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) : Bool :=
  finiteBoolDisjunction (fun sel : ThresholdRows.Selection a r =>
    selectionRow a r liveScale denominator input sel prime sample)

/-- The modular target the prime row approximates. -/
def primeModularTarget (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (input : BitInput r.q) {cutoff : ℕ} (prime : PrimeIndex cutoff) : Bool :=
  finiteBoolDisjunction (fun sel : ThresholdRows.Selection a r =>
    modularEquationHolds (ThresholdRows.equation a r sel) prime
      (fun index => ((thresholdFourfoldOccurrences r).get index).eval input))

theorem primeRow_mismatch_reciprocal (spectrum : ExpanderSpectrumContract)
    (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput r.q)
    {cutoff : ℕ} (prime : PrimeIndex cutoff) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            (thresholdFourfoldOccurrences r) liveScale denominator =>
          primeRow a r liveScale denominator input prime sample !=
            primeModularTarget a r input prime) ≤
      Fintype.card (ThresholdRows.Selection a r) *
        ((modulusDigitCount prime.val : ℝ) / (denominator + 1 : ℕ)) := by
  apply booleanMean_unionBound_uniform
    (fun sample : NormalizedOccurrenceListSeed
        (thresholdFourfoldOccurrences r) liveScale denominator =>
      primeRow a r liveScale denominator input prime sample !=
        primeModularTarget a r input prime)
    (fun sel sample =>
      selectionRow a r liveScale denominator input sel prime sample !=
        modularEquationHolds (ThresholdRows.equation a r sel) prime
          (fun index =>
            ((thresholdFourfoldOccurrences r).get index).eval input))
    ((modulusDigitCount prime.val : ℝ) / (denominator + 1 : ℕ))
  · intro sample hmismatch
    by_contra hnone
    have hall : ∀ sel : ThresholdRows.Selection a r,
        selectionRow a r liveScale denominator input sel prime sample =
          modularEquationHolds (ThresholdRows.equation a r sel) prime
            (fun index =>
              ((thresholdFourfoldOccurrences r).get index).eval input) := by
      intro sel
      generalize htarget :
          modularEquationHolds (ThresholdRows.equation a r sel) prime
            (fun index =>
              ((thresholdFourfoldOccurrences r).get index).eval input) =
            target
      cases happ :
          selectionRow a r liveScale denominator input sel prime sample <;>
        cases target
      · rfl
      · exfalso
        apply hnone
        refine ⟨sel, ?_⟩
        rw [happ, Bool.false_bne]
        exact htarget
      · exfalso
        apply hnone
        refine ⟨sel, ?_⟩
        rw [happ, Bool.true_bne, htarget]
        rfl
      · rfl
    have hequal :=
      finiteBoolDisjunction_congr
        (fun sel : ThresholdRows.Selection a r =>
          selectionRow a r liveScale denominator input sel prime sample)
        (fun sel : ThresholdRows.Selection a r =>
          modularEquationHolds (ThresholdRows.equation a r sel) prime
            (fun index =>
              ((thresholdFourfoldOccurrences r).get index).eval input))
        hall
    unfold primeRow primeModularTarget at hmismatch
    rw [hequal] at hmismatch
    simp at hmismatch
  · intro sel
    exact selectionRow_mismatch_reciprocal spectrum a r liveScale denominator
      input sel prime

/-! ## §4 The prime surrogate at the SELECTED Chebyshev contract

`CloseoutRawRows.thresholdPrimeCertificate` and this certificate are the same
`primeSurrogateCertificateFor theta (ThresholdRows.equation a r)` at the same
`canonicalPrimeCutoff`; only the magnitude exponent differs, because
`FourfoldRowPreprocessor.pointwise` admits no `r.circuits.length ≤ 4` side
condition and the family exponent needs none. -/

/-- Paper A.6 two-component reserve: one denominator pays for the prime
surrogate and the amplified list, once per child tuple. -/
def primeDenominator (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (target : ℕ) : ℕ :=
  reciprocalUnionDenominator (Fintype.card (ThresholdRows.Selection a r)) target

def primeCutoff (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (target : ℕ) : ℕ :=
  canonicalPrimeCutoff (familyMagnitudeExponent (ThresholdRows.equation a r))
    (primeDenominator a r target)

def listDenominator (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (target : ℕ) : ℕ :=
  modulusDigitCount (primeCutoff a r target) * (primeDenominator a r target + 1)

/-- The prime surrogate for the corrected source's child-equation family. -/
def certificate (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (target : ℕ) :
    PrimeSurrogateCertificate (ThresholdRows.Selection a r)
      (PrimeIndex (primeCutoff a r target))
      (Fin (thresholdFourfoldOccurrences r).length → Bool) :=
  tunedFiniteFamilyPrimeSurrogateCertificate theta (ThresholdRows.equation a r)
    (primeDenominator a r target)

/-- **The prime error (paper A.6).**  Same `canonicalPrimeError_le` engine as
`CloseoutRawRows.threshold_prime_error`. -/
theorem certificate_error_le (theta : PrimeThetaBoundContract)
    (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (target : ℕ) :
    (certificate theta a r target).error ≤
      1 / (primeDenominator a r target + 1 : ℕ) :=
  tunedFiniteFamilyPrimeSurrogateCertificate_error_le theta
    (ThresholdRows.equation a r) (primeDenominator a r target)

/-- **The list error (paper A.9 item 4).**  Mirrors
`CloseoutRawRows.threshold_list_error` at the request-derived cutoff. -/
theorem listUnionError_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (target : ℕ) :
    (modulusDigitCount (primeCutoff a r target) : ℝ) /
        (listDenominator a r target + 1 : ℕ) ≤
      1 / (primeDenominator a r target + 1 : ℕ) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  unfold listDenominator
  push_cast
  nlinarith

theorem primeModularTarget_mismatch_le (theta : PrimeThetaBoundContract)
    (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (input : BitInput r.q) (target : ℕ) :
    booleanMean
        (fun prime : PrimeIndex (primeCutoff a r target) =>
          primeModularTarget a r input prime !=
            conjunctionBit NormalizedThresholdThresholdCircuit.eval
              r.circuits input) ≤
      Fintype.card (ThresholdRows.Selection a r) *
        (certificate theta a r target).error := by
  let actual : Fin (thresholdFourfoldOccurrences r).length → Bool :=
    fun index => ((thresholdFourfoldOccurrences r).get index).eval input
  have hexact : ∀ sel : ThresholdRows.Selection a r,
      (certificate theta a r target).exact sel actual =
        exactRow a r sel input := by
    intro sel
    rfl
  have hmodular : ∀ sel : ThresholdRows.Selection a r,
      ∀ prime : PrimeIndex (primeCutoff a r target),
        (certificate theta a r target).modular sel prime actual =
          modularEquationHolds (ThresholdRows.equation a r sel) prime actual := by
    intro sel prime
    rfl
  by_cases htarget :
      conjunctionBit NormalizedThresholdThresholdCircuit.eval
        r.circuits input = true
  · have hdisjunction :
        finiteBoolDisjunction
            (fun sel : ThresholdRows.Selection a r => exactRow a r sel input) =
          true := by
      rw [exactDisjunction_eq_conjunction]
      exact htarget
    rcases (finiteBoolDisjunction_eq_true_iff _).mp hdisjunction with
      ⟨sel, hsel⟩
    have hprime : ∀ prime : PrimeIndex (primeCutoff a r target),
        primeModularTarget a r input prime = true := by
      intro prime
      apply (finiteBoolDisjunction_eq_true_iff _).mpr
      refine ⟨sel, ?_⟩
      rw [← hmodular sel prime]
      exact (certificate theta a r target).complete sel actual
        (by rw [hexact sel]; exact hsel) prime
    have hzero :
        booleanMean
            (fun prime : PrimeIndex (primeCutoff a r target) =>
              primeModularTarget a r input prime !=
                conjunctionBit NormalizedThresholdThresholdCircuit.eval
                  r.circuits input) = 0 := by
      unfold booleanMean
      have hsum :
          (∑ prime : PrimeIndex (primeCutoff a r target),
            bitAsReal
              (primeModularTarget a r input prime !=
                conjunctionBit NormalizedThresholdThresholdCircuit.eval
                  r.circuits input)) = 0 := by
        apply Finset.sum_eq_zero
        intro prime _
        rw [hprime prime, htarget]
        rfl
      rw [hsum]
      simp
    rw [hzero]
    exact mul_nonneg (by positivity)
      (certificate theta a r target).errorNonnegative
  · have htargetFalse :
        conjunctionBit NormalizedThresholdThresholdCircuit.eval
          r.circuits input = false :=
      Bool.eq_false_of_not_eq_true htarget
    apply booleanMean_unionBound_uniform
      (fun prime : PrimeIndex (primeCutoff a r target) =>
        primeModularTarget a r input prime !=
          conjunctionBit NormalizedThresholdThresholdCircuit.eval
            r.circuits input)
      (fun sel prime => (certificate theta a r target).modular sel prime actual)
      (certificate theta a r target).error
    · intro prime hmismatch
      have hmodularTarget : primeModularTarget a r input prime = true := by
        rw [htargetFalse, Bool.bne_false] at hmismatch
        exact hmismatch
      rcases (finiteBoolDisjunction_eq_true_iff _).mp hmodularTarget with
        ⟨sel, hsel⟩
      refine ⟨sel, ?_⟩
      rw [hmodular sel prime]
      exact hsel
    · intro sel
      apply (certificate theta a r target).sound sel actual
      intro haccepts
      have hsel : exactRow a r sel input = true := by
        rw [← hexact sel]
        exact haccepts
      have hdisjunction :
          finiteBoolDisjunction
            (fun candidate : ThresholdRows.Selection a r =>
              exactRow a r candidate input) = true :=
        (finiteBoolDisjunction_eq_true_iff _).mpr ⟨sel, hsel⟩
      rw [exactDisjunction_eq_conjunction] at hdisjunction
      exact htarget hdisjunction

/-! ## §5 The complete THR row and its closed reciprocal accuracy -/

/-- The complete threshold row: one canonical prime and one shared amplified
list seed, every disjoint child tuple aggregated by disjunction. -/
def fourfoldRow (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale target : ℕ) (input : BitInput r.q)
    (sample : PrimeIndex (primeCutoff a r target) ×
      NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
        (listDenominator a r target)) : Bool :=
  primeRow a r liveScale (listDenominator a r target) input sample.1 sample.2

theorem fourfoldRow_mismatch_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale target : ℕ) (input : BitInput r.q) :
    booleanMean
        (fun sample : PrimeIndex (primeCutoff a r target) ×
            NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r)
              liveScale (listDenominator a r target) =>
          fourfoldRow a r liveScale target input sample !=
            conjunctionBit NormalizedThresholdThresholdCircuit.eval
              r.circuits input) ≤
      Fintype.card (ThresholdRows.Selection a r) *
        ((modulusDigitCount (primeCutoff a r target) : ℝ) /
            (listDenominator a r target + 1 : ℕ) +
          (certificate theta a r target).error) := by
  have hlist :
      booleanMean
          (fun sample : PrimeIndex (primeCutoff a r target) ×
              NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r)
                liveScale (listDenominator a r target) =>
            fourfoldRow a r liveScale target input sample !=
              primeModularTarget a r input sample.1) ≤
        Fintype.card (ThresholdRows.Selection a r) *
          ((modulusDigitCount (primeCutoff a r target) : ℝ) /
            (listDenominator a r target + 1 : ℕ)) := by
    apply booleanMean_product_le_of_fiber
    · exact (certificate theta a r target).cardPositive
    · exact (normalizedOccurrenceListCertificate spectrum
        (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r target)).cardPositive
    · intro prime
      calc
        booleanMean
            (fun sample : NormalizedOccurrenceListSeed
                (thresholdFourfoldOccurrences r) liveScale
                  (listDenominator a r target) =>
              primeRow a r liveScale (listDenominator a r target) input prime
                  sample !=
                primeModularTarget a r input prime) ≤
            Fintype.card (ThresholdRows.Selection a r) *
              ((modulusDigitCount prime.val : ℝ) /
                (listDenominator a r target + 1 : ℕ)) :=
          primeRow_mismatch_reciprocal spectrum a r liveScale
            (listDenominator a r target) input prime
        _ ≤ Fintype.card (ThresholdRows.Selection a r) *
              ((modulusDigitCount (primeCutoff a r target) : ℝ) /
                (listDenominator a r target + 1 : ℕ)) := by
          gcongr
          exact_mod_cast Nat.succ_le_succ
            (Nat.log_mono_right (mem_primesUpTo.mp prime.property).2)
  have hprime :
      booleanMean
          (fun sample : PrimeIndex (primeCutoff a r target) ×
              NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r)
                liveScale (listDenominator a r target) =>
            primeModularTarget a r input sample.1 !=
              conjunctionBit NormalizedThresholdThresholdCircuit.eval
                r.circuits input) ≤
        Fintype.card (ThresholdRows.Selection a r) *
          (certificate theta a r target).error := by
    rw [booleanMean_product_left
      (fun prime : PrimeIndex (primeCutoff a r target) =>
        primeModularTarget a r input prime !=
          conjunctionBit NormalizedThresholdThresholdCircuit.eval
            r.circuits input)
      (certificate theta a r target).cardPositive
      (normalizedOccurrenceListCertificate spectrum
        (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r target)).cardPositive]
    exact primeModularTarget_mismatch_le theta a r input target
  calc
    _ ≤
        booleanMean
            (fun sample : PrimeIndex (primeCutoff a r target) ×
                NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r)
                  liveScale (listDenominator a r target) =>
              fourfoldRow a r liveScale target input sample !=
                primeModularTarget a r input sample.1) +
          booleanMean
            (fun sample : PrimeIndex (primeCutoff a r target) ×
                NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r)
                  liveScale (listDenominator a r target) =>
              primeModularTarget a r input sample.1 !=
                conjunctionBit NormalizedThresholdThresholdCircuit.eval
                  r.circuits input) :=
      booleanMean_mismatch_triangle
        (fun sample => fourfoldRow a r liveScale target input sample)
        (fun sample => primeModularTarget a r input sample.1)
        (fun _ => conjunctionBit NormalizedThresholdThresholdCircuit.eval
          r.circuits input)
    _ ≤ Fintype.card (ThresholdRows.Selection a r) *
          ((modulusDigitCount (primeCutoff a r target) : ℝ) /
            (listDenominator a r target + 1 : ℕ)) +
          Fintype.card (ThresholdRows.Selection a r) *
            (certificate theta a r target).error := by
      exact add_le_add hlist hprime
    _ = _ := by ring

/-- **The closed reciprocal accuracy (paper A.6 two-component ledger).**  The
mirror of `CloseoutRawRows.threshold_union_error`, at the ACTUAL tuple count. -/
theorem fourfoldRow_mismatch_reciprocal (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale target : ℕ) (input : BitInput r.q) :
    booleanMean
        (fun sample : PrimeIndex (primeCutoff a r target) ×
            NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r)
              liveScale (listDenominator a r target) =>
          fourfoldRow a r liveScale target input sample !=
            conjunctionBit NormalizedThresholdThresholdCircuit.eval
              r.circuits input) ≤
      1 / (target + 1 : ℕ) := by
  calc
    _ ≤ Fintype.card (ThresholdRows.Selection a r) *
        ((modulusDigitCount (primeCutoff a r target) : ℝ) /
            (listDenominator a r target + 1 : ℕ) +
          (certificate theta a r target).error) :=
      fourfoldRow_mismatch_le spectrum theta a r liveScale target input
    _ = (Fintype.card (ThresholdRows.Selection a r) : ℝ) *
        ((certificate theta a r target).error +
          (modulusDigitCount (primeCutoff a r target) : ℝ) /
            (listDenominator a r target + 1 : ℕ)) := by
      ring
    _ ≤ 1 / (target + 1 : ℕ) := by
      apply twoComponentUnionError_le
        (Fintype.card (ThresholdRows.Selection a r)) target
      · exact certificate_error_le theta a r target
      · exact listUnionError_le a r target

/-! ## §6 The deliverable: a `FourfoldRowPreprocessor` over `DecompositionAlgorithm` -/

/-- **THE THR ROWS.**  The exact analogue of
`SupplierEstimator.symmetricFourfoldRows`, over `DecompositionAlgorithm`
instead of `ExecutableExactDecompositionAlgorithm`.  Prime, list and
child-tuple union budgets are all derived from the request and the requested
accuracy; nothing is supplied by a caller. -/
def thresholdRows (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm)
    (liveScale : ℕ) (targetDenominator : ℕ → ℕ) :
    FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.eval where
  rowCount r :=
    Fintype.card
      (PrimeIndex (primeCutoff a r (targetDenominator r.q)) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r (targetDenominator r.q)))
  rowCountPositive r := by
    rw [Fintype.card_prod]
    exact Nat.mul_pos
      (certificate theta a r (targetDenominator r.q)).cardPositive
      (normalizedOccurrenceListCertificate spectrum
        (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r (targetDenominator r.q))).cardPositive
  row r index input :=
    fourfoldRow a r liveScale (targetDenominator r.q) input
      ((primeListSampleFinEquiv
        (cutoff := primeCutoff a r (targetDenominator r.q))
        (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r (targetDenominator r.q))).symm index)
  failure r := 1 / (targetDenominator r.q + 1 : ℕ)
  failureNonnegative _ := by positivity
  pointwise r input := by
    let Sample :=
      PrimeIndex (primeCutoff a r (targetDenominator r.q)) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r (targetDenominator r.q))
    let value : Sample → Bool := fun sample =>
      fourfoldRow a r liveScale (targetDenominator r.q) input sample !=
        conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input
    change
      booleanMean
          (fun index : Fin (Fintype.card Sample) =>
            value
              ((primeListSampleFinEquiv
                (cutoff := primeCutoff a r (targetDenominator r.q))
                (thresholdFourfoldOccurrences r) liveScale
                  (listDenominator a r (targetDenominator r.q))).symm index)) ≤
        1 / (targetDenominator r.q + 1 : ℕ)
    calc
      _ = booleanMean value :=
        booleanMean_equivFin Sample
          (primeListSampleFinEquiv
            (cutoff := primeCutoff a r (targetDenominator r.q))
            (thresholdFourfoldOccurrences r) liveScale
              (listDenominator a r (targetDenominator r.q)))
          value
      _ ≤ 1 / (targetDenominator r.q + 1 : ℕ) :=
        fourfoldRow_mismatch_reciprocal spectrum theta a r liveScale
          (targetDenominator r.q) input

theorem thresholdRows_of_decomposition (sources : EightSources)
    (liveScale : ℕ) (targetDenominator : ℕ → ℕ) :
    ∃ rows : FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
        NormalizedThresholdThresholdCircuit.eval,
      ∀ request : FourfoldRequest NormalizedThresholdThresholdCircuit,
        rows.failure request =
          (1 : ℝ) / ((targetDenominator request.q + 1 : ℕ) : ℝ) :=
  ⟨thresholdRows (expanderOf sources) (primeOf sources)
      (decompositionOf sources) liveScale targetDenominator, fun _ => rfl⟩

theorem thresholdRows_failure_le (sources : EightSources)
    {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (ph : CloseoutRowsOriginalSchedule.Phase) (mass : ℚ)
    (liveScale n : ℕ) (circuits : List (NormalizedThresholdThresholdCircuit n)) :
    (thresholdRows (expanderOf sources) (primeOf sources)
        (decompositionOf sources) liveScale (fun _ =>
          CloseoutFinalC10SupplierAccuracy.toleranceDenominator constants ph
            mass)).failure ⟨n, circuits⟩ ≤
      (1 : ℝ) / ((CloseoutFinalC10SupplierAccuracy.toleranceDenominator
        constants ph mass + 1 : ℕ) : ℝ) :=
  le_of_eq rfl

/-- **The THR supplier's point accuracy at the eight sources.**  Composing the
rows with `RepairCloseoutFinalC10SupplierAccuracy.rowSupplier_error_le` gives
`Realizes.hpoint` for the threshold mode with no ninth assumption. -/
theorem thresholdSupplier_error_le (sources : EightSources)
    (liveScale target n : ℕ)
    (circuits : List (NormalizedThresholdThresholdCircuit n)) :
    |((CloseoutFinalC10SupplierAccuracy.rowSupplier
            (thresholdRows (expanderOf sources) (primeOf sources)
              (decompositionOf sources) liveScale fun _ => target)
            n circuits : ℚ) : ℝ) -
        conjunctionProbability NormalizedThresholdThresholdCircuit.eval
          circuits| ≤ (1 : ℝ) / ((target + 1 : ℕ) : ℝ) :=
  CloseoutFinalC10SupplierAccuracy.rowSupplier_error_le _ n circuits

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows
