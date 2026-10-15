import Proof.CaseAnalysis.FinalThresholdRowIdentity
import Proof.CaseAnalysis.FinalPrinterBridge
import Proof.CaseAnalysis.RawRowsLeaf

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open scoped BigOperators
open NearCubicWires
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierRadix
open NearCubicWires.SupplierWalk
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.CloseoutRawRows

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdParityRow

noncomputable section

section Accuracy

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-- **A.13.1, parity form.** -/
theorem exactParity_eq_conjunction (input : BitInput r.q) :
    boolParity (fun sel : ThresholdRows.Selection a r =>
        CloseoutFinalC10ThresholdRows.exactRow a r sel input) =
      conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input := by
  unfold boolParity
  rw [CloseoutFinalC10ThresholdRows.exactRow_sum a r input]
  cases conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input <;> simp

/-! ## §2 One prime's parity row and its amplified-list error

The proof is the SAME union bound as `primeRow_mismatch_reciprocal`
(`Proof/CaseAnalysis/FinalThresholdRows.lean`): if every printed component agrees with its
modular target then the aggregates agree.  Only the aggregation congruence changes —
`finiteBoolDisjunction_congr` becomes `congrArg boolParity`. -/

/-- The GF(2) parity aggregate of the printed per-`g` rows at one prime and one list seed. -/
def parityPrimeRow (liveScale denominator : ℕ) (input : BitInput r.q)
    {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) : Bool :=
  boolParity (fun sel : ThresholdRows.Selection a r =>
    CloseoutFinalC10ThresholdRows.selectionRow a r liveScale denominator input sel prime sample)

/-- The modular target the parity row approximates. -/
def parityModularTarget (input : BitInput r.q) {cutoff : ℕ}
    (prime : PrimeIndex cutoff) : Bool :=
  boolParity (fun sel : ThresholdRows.Selection a r =>
    modularEquationHolds (ThresholdRows.equation a r sel) prime
      (fun index => ((thresholdFourfoldOccurrences r).get index).eval input))

theorem parityPrimeRow_mismatch_reciprocal (spectrum : ExpanderSpectrumContract)
    (liveScale denominator : ℕ) (input : BitInput r.q)
    {cutoff : ℕ} (prime : PrimeIndex cutoff) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            (thresholdFourfoldOccurrences r) liveScale denominator =>
          parityPrimeRow a r liveScale denominator input prime sample !=
            parityModularTarget a r input prime) ≤
      Fintype.card (ThresholdRows.Selection a r) *
        ((modulusDigitCount prime.val : ℝ) / (denominator + 1 : ℕ)) := by
  apply booleanMean_unionBound_uniform
    (fun sample : NormalizedOccurrenceListSeed
        (thresholdFourfoldOccurrences r) liveScale denominator =>
      parityPrimeRow a r liveScale denominator input prime sample !=
        parityModularTarget a r input prime)
    (fun sel sample =>
      CloseoutFinalC10ThresholdRows.selectionRow a r liveScale denominator input sel prime
          sample !=
        modularEquationHolds (ThresholdRows.equation a r sel) prime
          (fun index => ((thresholdFourfoldOccurrences r).get index).eval input))
    ((modulusDigitCount prime.val : ℝ) / (denominator + 1 : ℕ))
  · intro sample hmismatch
    by_contra hnone
    have hall : ∀ sel : ThresholdRows.Selection a r,
        CloseoutFinalC10ThresholdRows.selectionRow a r liveScale denominator input sel prime
            sample =
          modularEquationHolds (ThresholdRows.equation a r sel) prime
            (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) := by
      intro sel
      by_contra hne
      exact hnone ⟨sel, by simpa using hne⟩
    have hequal :
        parityPrimeRow a r liveScale denominator input prime sample =
          parityModularTarget a r input prime :=
      congrArg boolParity (funext hall)
    rw [hequal] at hmismatch
    simp at hmismatch
  · intro sel
    exact CloseoutFinalC10ThresholdRows.selectionRow_mismatch_reciprocal spectrum a r liveScale
      denominator input sel prime

/-- **The per-`g` disagreement bound.**  For every child tuple the prime surrogate differs from
the exact child row on at most an `error` fraction of the sampled primes: on the accepting tuple
the certificate's COMPLETENESS makes the disagreement empty, and on every rejecting tuple its
SOUNDNESS bounds the disagreement in mean.  No disjointness is used. -/
theorem certificate_disagreement_le (theta : PrimeThetaBoundContract)
    (input : BitInput r.q) (target : ℕ) (sel : ThresholdRows.Selection a r) :
    booleanMean
        (fun prime : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) =>
          modularEquationHolds (ThresholdRows.equation a r sel) prime
              (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) !=
            CloseoutFinalC10ThresholdRows.exactRow a r sel input) ≤
      (CloseoutFinalC10ThresholdRows.certificate theta a r target).error := by
  have hexact :
      (CloseoutFinalC10ThresholdRows.certificate theta a r target).exact sel
          (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) =
        CloseoutFinalC10ThresholdRows.exactRow a r sel input := rfl
  have hmodular : ∀ prime : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target),
      (CloseoutFinalC10ThresholdRows.certificate theta a r target).modular sel prime
          (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) =
        modularEquationHolds (ThresholdRows.equation a r sel) prime
          (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) := by
    intro prime
    rfl
  cases hcase : CloseoutFinalC10ThresholdRows.exactRow a r sel input
  · simp only [Bool.bne_false]
    exact (CloseoutFinalC10ThresholdRows.certificate theta a r target).sound sel
      (fun index => ((thresholdFourfoldOccurrences r).get index).eval input)
      (by rw [hexact, hcase]; simp)
  · have hall : ∀ prime : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target),
        modularEquationHolds (ThresholdRows.equation a r sel) prime
            (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) = true := by
      intro prime
      rw [← hmodular prime]
      exact (CloseoutFinalC10ThresholdRows.certificate theta a r target).complete sel
        (fun index => ((thresholdFourfoldOccurrences r).get index).eval input)
        (by rw [hexact, hcase]) prime
    have hfun :
        (fun prime : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) =>
            (modularEquationHolds (ThresholdRows.equation a r sel) prime
              (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) !=
                true)) =
          fun _ : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) => false := by
      funext prime
      rw [hall prime]
      rfl
    rw [hfun]
    have hzero :
        booleanMean
            (fun _ : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) =>
              false) = 0 := by
      unfold booleanMean
      simp [bitAsReal]
    rw [hzero]
    exact (CloseoutFinalC10ThresholdRows.certificate theta a r target).errorNonnegative

/-- **The parity modular target against the fourfold conjunction.**  Union bound over the paper's
`g`, at the SAME budget `|\mathcal G| × error` the disjunction route pays
(`primeModularTarget_mismatch_le`, `Proof/CaseAnalysis/FinalThresholdRows.lean`). -/
theorem parityModularTarget_mismatch_le (theta : PrimeThetaBoundContract)
    (input : BitInput r.q) (target : ℕ) :
    booleanMean
        (fun prime : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) =>
          parityModularTarget a r input prime !=
            conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input) ≤
      Fintype.card (ThresholdRows.Selection a r) *
        (CloseoutFinalC10ThresholdRows.certificate theta a r target).error := by
  apply booleanMean_unionBound_uniform
    (fun prime : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) =>
      parityModularTarget a r input prime !=
        conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input)
    (fun sel prime =>
      modularEquationHolds (ThresholdRows.equation a r sel) prime
          (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) !=
        CloseoutFinalC10ThresholdRows.exactRow a r sel input)
    (CloseoutFinalC10ThresholdRows.certificate theta a r target).error
  · intro prime hmismatch
    by_contra hnone
    have hall : ∀ sel : ThresholdRows.Selection a r,
        modularEquationHolds (ThresholdRows.equation a r sel) prime
            (fun index => ((thresholdFourfoldOccurrences r).get index).eval input) =
          CloseoutFinalC10ThresholdRows.exactRow a r sel input := by
      intro sel
      by_contra hne
      exact hnone ⟨sel, by simpa using hne⟩
    have hequal :
        parityModularTarget a r input prime =
          boolParity (fun sel : ThresholdRows.Selection a r =>
            CloseoutFinalC10ThresholdRows.exactRow a r sel input) :=
      congrArg boolParity (funext hall)
    rw [hequal, exactParity_eq_conjunction] at hmismatch
    simp at hmismatch
  · intro sel
    exact certificate_disagreement_le a r theta input target sel

/-! ## §4 The complete parity row and its closed reciprocal accuracy -/

/-- **THE PARITY ROW.**  One canonical prime, one shared amplified-list seed, and the paper's
child tuples aggregated by the GF(2) sum of A.13.10 rather than by disjunction.  The row index is
still `(p,e)`, so A.13.10's `1/(|\mathcal P_q||\mathcal E|2^q)` normalisation is unchanged. -/
def parityRow (liveScale target : ℕ) (input : BitInput r.q)
    (sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
      NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator a r target)) : Bool :=
  parityPrimeRow a r liveScale (CloseoutFinalC10ThresholdRows.listDenominator a r target) input
    sample.1 sample.2

theorem parityRow_mismatch_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ) (input : BitInput r.q) :
    booleanMean
        (fun sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
            NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
              (CloseoutFinalC10ThresholdRows.listDenominator a r target) =>
          parityRow a r liveScale target input sample !=
            conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input) ≤
      Fintype.card (ThresholdRows.Selection a r) *
        ((modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) : ℝ) /
            (CloseoutFinalC10ThresholdRows.listDenominator a r target + 1 : ℕ) +
          (CloseoutFinalC10ThresholdRows.certificate theta a r target).error) := by
  have hlist :
      booleanMean
          (fun sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
              NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
                (CloseoutFinalC10ThresholdRows.listDenominator a r target) =>
            parityRow a r liveScale target input sample !=
              parityModularTarget a r input sample.1) ≤
        Fintype.card (ThresholdRows.Selection a r) *
          ((modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) : ℝ) /
            (CloseoutFinalC10ThresholdRows.listDenominator a r target + 1 : ℕ)) := by
    apply booleanMean_product_le_of_fiber
    · exact (CloseoutFinalC10ThresholdRows.certificate theta a r target).cardPositive
    · exact (normalizedOccurrenceListCertificate spectrum
        (thresholdFourfoldOccurrences r) liveScale
          (CloseoutFinalC10ThresholdRows.listDenominator a r target)).cardPositive
    · intro prime
      calc
        booleanMean
            (fun sample : NormalizedOccurrenceListSeed
                (thresholdFourfoldOccurrences r) liveScale
                  (CloseoutFinalC10ThresholdRows.listDenominator a r target) =>
              parityPrimeRow a r liveScale
                  (CloseoutFinalC10ThresholdRows.listDenominator a r target) input prime
                  sample !=
                parityModularTarget a r input prime) ≤
            Fintype.card (ThresholdRows.Selection a r) *
              ((modulusDigitCount prime.val : ℝ) /
                (CloseoutFinalC10ThresholdRows.listDenominator a r target + 1 : ℕ)) :=
          parityPrimeRow_mismatch_reciprocal a r spectrum liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r target) input prime
        _ ≤ Fintype.card (ThresholdRows.Selection a r) *
              ((modulusDigitCount
                  (CloseoutFinalC10ThresholdRows.primeCutoff a r target) : ℝ) /
                (CloseoutFinalC10ThresholdRows.listDenominator a r target + 1 : ℕ)) := by
          gcongr
          exact_mod_cast Nat.succ_le_succ
            (Nat.log_mono_right (mem_primesUpTo.mp prime.property).2)
  have hprime :
      booleanMean
          (fun sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
              NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
                (CloseoutFinalC10ThresholdRows.listDenominator a r target) =>
            parityModularTarget a r input sample.1 !=
              conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input) ≤
        Fintype.card (ThresholdRows.Selection a r) *
          (CloseoutFinalC10ThresholdRows.certificate theta a r target).error := by
    rw [booleanMean_product_left
      (fun prime : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) =>
        parityModularTarget a r input prime !=
          conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input)
      (CloseoutFinalC10ThresholdRows.certificate theta a r target).cardPositive
      (normalizedOccurrenceListCertificate spectrum
        (thresholdFourfoldOccurrences r) liveScale
          (CloseoutFinalC10ThresholdRows.listDenominator a r target)).cardPositive]
    exact parityModularTarget_mismatch_le a r theta input target
  calc
    _ ≤
        booleanMean
            (fun sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
                NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
                  (CloseoutFinalC10ThresholdRows.listDenominator a r target) =>
              parityRow a r liveScale target input sample !=
                parityModularTarget a r input sample.1) +
          booleanMean
            (fun sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
                NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
                  (CloseoutFinalC10ThresholdRows.listDenominator a r target) =>
              parityModularTarget a r input sample.1 !=
                conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input) :=
      booleanMean_mismatch_triangle
        (fun sample => parityRow a r liveScale target input sample)
        (fun sample => parityModularTarget a r input sample.1)
        (fun _ => conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input)
    _ ≤ Fintype.card (ThresholdRows.Selection a r) *
          ((modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) : ℝ) /
            (CloseoutFinalC10ThresholdRows.listDenominator a r target + 1 : ℕ)) +
          Fintype.card (ThresholdRows.Selection a r) *
            (CloseoutFinalC10ThresholdRows.certificate theta a r target).error :=
      add_le_add hlist hprime
    _ = _ := by ring

/-- **THE LOAD-BEARING STATEMENT.**  `FourfoldRowPreprocessor.pointwise`
(`Proof/Supplier/SupplierEstimator.lean`) at the PARITY row: the mean mismatch of the GF(2)
aggregate of the printed per-`g` rows against `conjunctionBit` is within the requested
`1/(target+1)`.  This is what THRB warned an honest `(g,p,e)`-indexed family cannot give (its
mismatch mean is `≥ (|G|-1)/|G|` at an accepting input); the parity row keeps the row index
`(p,e)`, and the bound is the disjunction row's own two-component union budget. -/
theorem parityRow_pointwise (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ) (input : BitInput r.q) :
    booleanMean
        (fun sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
            NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
              (CloseoutFinalC10ThresholdRows.listDenominator a r target) =>
          boolParity
              (fun sel : ThresholdRows.Selection a r =>
                CloseoutFinalC10ThresholdRows.selectionRow a r liveScale
                  (CloseoutFinalC10ThresholdRows.listDenominator a r target) input sel sample.1
                  sample.2) !=
            conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input) ≤
      1 / (target + 1 : ℕ) := by
  show
    booleanMean
        (fun sample : PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target) ×
            NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
              (CloseoutFinalC10ThresholdRows.listDenominator a r target) =>
          parityRow a r liveScale target input sample !=
            conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input) ≤
      1 / (target + 1 : ℕ)
  calc
    _ ≤ Fintype.card (ThresholdRows.Selection a r) *
        ((modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) : ℝ) /
            (CloseoutFinalC10ThresholdRows.listDenominator a r target + 1 : ℕ) +
          (CloseoutFinalC10ThresholdRows.certificate theta a r target).error) :=
      parityRow_mismatch_le a r spectrum theta liveScale target input
    _ = (Fintype.card (ThresholdRows.Selection a r) : ℝ) *
        ((CloseoutFinalC10ThresholdRows.certificate theta a r target).error +
          (modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) : ℝ) /
            (CloseoutFinalC10ThresholdRows.listDenominator a r target + 1 : ℕ)) := by
      ring
    _ ≤ 1 / (target + 1 : ℕ) := by
      apply twoComponentUnionError_le
        (Fintype.card (ThresholdRows.Selection a r)) target
      · exact CloseoutFinalC10ThresholdRows.certificate_error_le theta a r target
      · exact CloseoutFinalC10ThresholdRows.listUnionError_le a r target

end Accuracy

/-! ## §5 The deliverable rows object

`CloseoutFinalC10ThresholdRows.thresholdRows` (`Proof/CaseAnalysis/FinalThresholdRows.lean`)
with the `g`-aggregate changed from `finiteBoolDisjunction` to `boolParity`.  `rowCount`,
`failure` and the external row index are IDENTICAL, so A.13.10's
`1/(|\mathcal P_q||\mathcal E|2^q)` normalisation is unchanged and every consumer of the
preprocessor interface — `rowAnswer`, `rowDenominator`, `answer`, `rowSupplier_error_le` — applies
verbatim. -/

section Rows

/-- **THE PARITY ROWS.** -/
def parityRows (spectrum : ExpanderSpectrumContract) (theta : PrimeThetaBoundContract)
    (a : DecompositionAlgorithm) (liveScale : ℕ) (targetDenominator : ℕ → ℕ) :
    FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.eval where
  rowCount request :=
    Fintype.card
      (PrimeIndex
          (CloseoutFinalC10ThresholdRows.primeCutoff a request
            (targetDenominator request.q)) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences request) liveScale
          (CloseoutFinalC10ThresholdRows.listDenominator a request
            (targetDenominator request.q)))
  rowCountPositive request := by
    rw [Fintype.card_prod]
    exact Nat.mul_pos
      (CloseoutFinalC10ThresholdRows.certificate theta a request
        (targetDenominator request.q)).cardPositive
      (normalizedOccurrenceListCertificate spectrum
        (thresholdFourfoldOccurrences request) liveScale
          (CloseoutFinalC10ThresholdRows.listDenominator a request
            (targetDenominator request.q))).cardPositive
  row request index input :=
    parityRow a request liveScale (targetDenominator request.q) input
      ((primeListSampleFinEquiv
        (cutoff :=
          CloseoutFinalC10ThresholdRows.primeCutoff a request (targetDenominator request.q))
        (thresholdFourfoldOccurrences request) liveScale
          (CloseoutFinalC10ThresholdRows.listDenominator a request
            (targetDenominator request.q))).symm index)
  failure request := 1 / (targetDenominator request.q + 1 : ℕ)
  failureNonnegative _ := by positivity
  pointwise request input := by
    let Sample :=
      PrimeIndex
          (CloseoutFinalC10ThresholdRows.primeCutoff a request
            (targetDenominator request.q)) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences request) liveScale
          (CloseoutFinalC10ThresholdRows.listDenominator a request
            (targetDenominator request.q))
    let value : Sample → Bool := fun sample =>
      parityRow a request liveScale (targetDenominator request.q) input sample !=
        conjunctionBit NormalizedThresholdThresholdCircuit.eval request.circuits input
    change
      booleanMean
          (fun index : Fin (Fintype.card Sample) =>
            value
              ((primeListSampleFinEquiv
                (cutoff :=
                  CloseoutFinalC10ThresholdRows.primeCutoff a request
                    (targetDenominator request.q))
                (thresholdFourfoldOccurrences request) liveScale
                  (CloseoutFinalC10ThresholdRows.listDenominator a request
                    (targetDenominator request.q))).symm index)) ≤
        1 / (targetDenominator request.q + 1 : ℕ)
    calc
      _ = booleanMean value :=
        booleanMean_equivFin Sample
          (primeListSampleFinEquiv
            (cutoff :=
              CloseoutFinalC10ThresholdRows.primeCutoff a request
                (targetDenominator request.q))
            (thresholdFourfoldOccurrences request) liveScale
              (CloseoutFinalC10ThresholdRows.listDenominator a request
                (targetDenominator request.q)))
          value
      _ ≤ 1 / (targetDenominator request.q + 1 : ℕ) :=
        parityRow_pointwise a request spectrum theta liveScale (targetDenominator request.q)
          input

/-- The parity rows have exactly the row count of `thresholdRows`
(`C10ThresholdRowIdentity.thresholdRows_rowCount`,
`Proof/CaseAnalysis/FinalThresholdRowIdentity.lean`): the prime `p` and the amplified-list seed
`e`, with no `Fintype.card (ThresholdRows.Selection a r)` factor. -/
theorem parityRows_rowCount (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (parityRows spectrum theta a liveScale targetDenominator).rowCount r =
      Fintype.card
        (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r (targetDenominator r.q)) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r (targetDenominator r.q))) := by
  simp only [parityRows]

/-- The failure is the caller's requested reciprocal accuracy, the same as
`thresholdRows.failure`. -/
theorem parityRows_failure (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (parityRows spectrum theta a liveScale targetDenominator).failure r =
      1 / (targetDenominator r.q + 1 : ℕ) := by
  simp only [parityRows]

theorem parityRows_row (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (index : Fin ((parityRows spectrum theta a liveScale targetDenominator).rowCount r))
    (input : BitInput r.q) :
    (parityRows spectrum theta a liveScale targetDenominator).row r index input =
      parityRow a r liveScale (targetDenominator r.q) input
        ((primeListSampleFinEquiv
          (cutoff := CloseoutFinalC10ThresholdRows.primeCutoff a r (targetDenominator r.q))
          (thresholdFourfoldOccurrences r) liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r (targetDenominator r.q))).symm
          (Fin.cast (parityRows_rowCount spectrum theta a liveScale targetDenominator r)
            index)) := by
  simp only [parityRows]
  rfl

/-- `FourfoldRowPreprocessor.aggregation` (`Proof/Supplier/SupplierEstimator.lean`) and
`FiniteRowAggregation.acceptanceCount` (`:4432`) unfolded for ANY preprocessor: the count is the
double sum over the external row index and all `q`-bit inputs. -/
theorem acceptanceCount_unfold {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (preprocessor : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) :
    (preprocessor.aggregation request).acceptanceCount =
      ∑ index : Fin (preprocessor.rowCount request), ∑ input : BitInput request.q,
        (preprocessor.row request index input).toNat :=
  rfl

end Rows

/-! ## §6 The printed parity row — ONE polynomial per `(p,e)`, ADDITIVE in `|G|` -/

section Printed

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-- The enumeration of the paper's external label `g` used by the printed parity row. -/
def selectionEnum :
    ThresholdRows.Selection a r ≃ Fin (Fintype.card (ThresholdRows.Selection a r)) :=
  Fintype.equivFin (ThresholdRows.Selection a r)

/-- **THE PRINTED PARITY ROW.**  The GF(2) sum over the paper's `g` of A.13.7's
`Q_{g,p,e,f}` = `thresholdRow a r sel …` (`Proof/CaseAnalysis/RawRowsModes.lean`), at the offset
family `f_{g,p}` of A.13.10.  One polynomial per `(p,e)`. -/
def printedParityRow (liveScale denominator modulus : ℕ)
    (offset : ThresholdRows.Selection a r → ℕ)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity
    (fun index : Fin (Fintype.card (ThresholdRows.Selection a r)) =>
      thresholdRow a r ((selectionEnum a r).symm index) liveScale denominator modulus
        (offset ((selectionEnum a r).symm index)) seed)

theorem printedParityRow_length (liveScale denominator modulus : ℕ)
    (offset : ThresholdRows.Selection a r → ℕ)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    (printedParityRow a r liveScale denominator modulus offset seed).length =
      ∑ sel : ThresholdRows.Selection a r,
        (thresholdRow a r sel liveScale denominator modulus (offset sel) seed).length := by
  unfold printedParityRow
  rw [parity_length]
  exact Equiv.sum_comp (selectionEnum a r).symm
    (fun sel : ThresholdRows.Selection a r =>
      (thresholdRow a r sel liveScale denominator modulus (offset sel) seed).length)

/-- **THE PRINTED-FORM IDENTITY.**  Evaluating the printed parity row on A.2's coded
occurrence-residual variables returns the GF(2) parity of the `|G|` estimator tuple rows — i.e.
the row VALUE of `parityRow`.  Uses `evaluateStructuralGF2_finParity`
(`Proof/MachineModel/CanonicalFourfoldRowProgram.lean`), `boolParity_equiv` (`:996`) and the per-`g`
identity `thresholdRow_eq_selectionRow`
(`Proof/CaseAnalysis/FinalThresholdRowIdentity.lean`). -/
theorem parityRow_eq_canonical (liveScale denominator : ℕ) (input : BitInput r.q)
    {cutoff : ℕ} (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable (thresholdFourfoldOccurrences r)
            (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) input index)
        (printedParityRow a r liveScale denominator prime.val
          (fun sel =>
            modularResidualOffset (thresholdFourfoldOccurrences r) liveScale input
              (ThresholdRows.equation a r sel) prime.val)
          seed) =
      boolParity (fun sel : ThresholdRows.Selection a r =>
        CloseoutFinalC10ThresholdRows.selectionRow a r liveScale denominator input sel prime
          seed) := by
  unfold printedParityRow
  rw [evaluateStructuralGF2_finParity]
  rw [← boolParity_equiv (selectionEnum a r).symm
    (fun sel : ThresholdRows.Selection a r =>
      CloseoutFinalC10ThresholdRows.selectionRow a r liveScale denominator input sel prime seed)]
  exact congrArg boolParity
    (funext fun index =>
      C10ThresholdRowIdentity.thresholdRow_eq_selectionRow a r liveScale denominator input
        ((selectionEnum a r).symm index) prime seed)

end Printed

/-! ## §7 The bridge: `acceptanceCount` as a sum of printed exact column counts

The THR twin of `C10PrinterBridge.acceptanceCount_eq_sum_exactColumnCount`
(`Proof/CaseAnalysis/FinalPrinterBridge.lean`).  A.2's live/residual split is the same
`normalizedLiveExternalInputEquiv` (`Proof/Supplier/SupplierEstimator.lean`); the offset selected
by the residual column is A.13.10's `f_{g,p}(z)`, and it is a function of `z` ALONE because
`modularResidualOffset` reads the input only through `occurrenceResidualConstant`, i.e. through
`frozenScore`, which sums over `Finset.univ \ live`. -/

section Split

/-- A.2's reassembly at a general live set. -/
def splitInput {q : ℕ} (live : Finset (Fin q)) (y : BitInput live.card)
    (z : BitInput liveᶜ.card) : BitInput q :=
  (normalizedLiveExternalInputEquiv live).symm (y, z)

theorem splitInput_eq_elim {q : ℕ} (live : Finset (Fin q)) (y : BitInput live.card)
    (z : BitInput liveᶜ.card) :
    splitInput live y z =
      fun coordinate =>
        Sum.elim y z ((normalizedLiveExternalCoordinateEquiv live).symm coordinate) := by
  unfold splitInput normalizedLiveExternalInputEquiv bitInputSumEquiv
  funext coordinate
  simp [Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

theorem coordinateEquiv_inl_mem {q : ℕ} (live : Finset (Fin q)) (index : Fin live.card) :
    normalizedLiveExternalCoordinateEquiv live (Sum.inl index) ∈ live := by
  unfold normalizedLiveExternalCoordinateEquiv
  rw [finSumEquivOfFinset_inl]
  exact Finset.orderEmbOfFin_mem _ rfl index

/-- Off the live set the reassembled input depends on `z` alone. -/
theorem splitInput_congr_of_not_mem {q : ℕ} (live : Finset (Fin q))
    (y y' : BitInput live.card) (z : BitInput liveᶜ.card) (coordinate : Fin q)
    (hcoordinate : coordinate ∉ live) :
    splitInput live y z coordinate = splitInput live y' z coordinate := by
  rw [splitInput_eq_elim, splitInput_eq_elim]
  dsimp only
  rcases hsplit : (normalizedLiveExternalCoordinateEquiv live).symm coordinate with index | index
  · exfalso
    apply hcoordinate
    rw [(Equiv.symm_apply_eq _).mp hsplit]
    exact coordinateEquiv_inl_mem live index
  · rfl

/-- The signed frozen constant reads the input only off the live set (A.2: "\(C_i\) ignores
\(I\)"), via `C10PrinterBridge.residualConstant_congr`
(`Proof/CaseAnalysis/FinalPrinterBridge.lean`). -/
theorem occurrenceWeightedResidualConstant_congr {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) (liveScale : ℕ)
    (left right : BitInput q)
    (hequal : ∀ index, index ∉ normalizedLiveSet occurrences liveScale →
      left index = right index)
    (mask : Finset (Fin occurrences.length)) (weight : Fin occurrences.length → ℤ) :
    occurrenceWeightedResidualConstant occurrences liveScale left mask weight =
      occurrenceWeightedResidualConstant occurrences liveScale right mask weight := by
  unfold occurrenceWeightedResidualConstant occurrenceResidualConstant
  apply Finset.sum_congr rfl
  intro index _
  rw [C10PrinterBridge.residualConstant_congr _ _ left right hequal]

/-- A.13.10's `f_{g,p}(z)` is a function of the residual column alone. -/
theorem modularResidualOffset_congr {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) (liveScale : ℕ)
    (left right : BitInput q)
    (hequal : ∀ index, index ∉ normalizedLiveSet occurrences liveScale →
      left index = right index)
    (equation : LabelledEquation (Fin occurrences.length)) (modulus : ℕ) :
    modularResidualOffset occurrences liveScale left equation modulus =
      modularResidualOffset occurrences liveScale right equation modulus := by
  unfold modularResidualOffset
  rw [occurrenceWeightedResidualConstant_congr occurrences liveScale left right hequal]

end Split

section Bridge

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-- `holds`: A.2's residual variable \(Z_i(y,z)\) of the coded occurrence `code`, in the ABI of
`encodedFiniteBooleanAssignment`. -/
def thrHolds (liveScale : ℕ) (code : ℕ)
    (y : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card) :
    Bool :=
  encodedFiniteBooleanAssignment
    (fun index =>
      occurrenceResidualVariable (thresholdFourfoldOccurrences r)
        (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
        (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z) index)
    code

/-- **A.13.10's \(f_{g,p}(z)\)**: the modular offset the fixed-column scan selects, a function of
the residual column `z` and the external label `g` only. -/
def thrOffset (liveScale : ℕ)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card)
    (sel : ThresholdRows.Selection a r) (modulus : ℕ) : ℕ :=
  modularResidualOffset (thresholdFourfoldOccurrences r) liveScale
    (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
      (fun _ => false) z)
    (ThresholdRows.equation a r sel) modulus

theorem thrOffset_spec (liveScale : ℕ)
    (y : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card)
    (sel : ThresholdRows.Selection a r) (modulus : ℕ) :
    modularResidualOffset (thresholdFourfoldOccurrences r) liveScale
        (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z)
        (ThresholdRows.equation a r sel) modulus =
      thrOffset a r liveScale z sel modulus := by
  unfold thrOffset
  exact modularResidualOffset_congr _ _ _ _
    (fun coordinate hcoordinate =>
      splitInput_congr_of_not_mem _ y (fun _ => false) z coordinate hcoordinate) _ _

theorem printedParityRow_offset (liveScale denominator modulus : ℕ)
    (y : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator) :
    printedParityRow a r liveScale denominator modulus
        (fun sel => thrOffset a r liveScale z sel modulus) seed =
      printedParityRow a r liveScale denominator modulus
        (fun sel =>
          modularResidualOffset (thresholdFourfoldOccurrences r) liveScale
            (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z)
            (ThresholdRows.equation a r sel) modulus)
        seed := by
  congr 1
  funext sel
  exact (thrOffset_spec a r liveScale y z sel modulus).symm

/-- The printed parity row at live block `y` and residual column `z` IS the parity row value at
the reassembled input. -/
theorem exactPolynomialValue_printedParityRow (liveScale denominator : ℕ) {cutoff : ℕ}
    (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator)
    (y : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card) :
    exactPolynomialValue (thrHolds r liveScale)
        (printedParityRow a r liveScale denominator prime.val
          (fun sel => thrOffset a r liveScale z sel prime.val) seed) y z =
      parityPrimeRow a r liveScale denominator
        (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z)
        prime seed := by
  rw [printedParityRow_offset a r liveScale denominator prime.val y z seed,
    ← C10PrinterBridge.evaluateStructuralGF2_eq_exactPolynomialValue]
  exact parityRow_eq_canonical a r liveScale denominator
    (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z) prime seed

/-- **A.13.10's \(T_{g,p,e,f}(z)\), GF(2)-summed over `g`**: the exact column count of the printed
parity row is the live-cube sum of the parity row value. -/
theorem exactColumnCount_printedParityRow (liveScale denominator : ℕ) {cutoff : ℕ}
    (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences r) liveScale denominator)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card) :
    exactColumnCount (thrHolds r liveScale)
        (printedParityRow a r liveScale denominator prime.val
          (fun sel => thrOffset a r liveScale z sel prime.val) seed) z =
      ∑ y : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card,
        (parityPrimeRow a r liveScale denominator
          (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z)
          prime seed).toNat := by
  unfold exactColumnCount
  apply Finset.sum_congr rfl
  intro y _
  rw [exactPolynomialValue_printedParityRow]

theorem thrAcceptanceCount_eq_sum_parity (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale : ℕ) (targetDenominator : ℕ → ℕ) :
    ((parityRows spectrum theta a liveScale targetDenominator).aggregation r).acceptanceCount =
      ∑ sample :
          PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r (targetDenominator r.q)) ×
            NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
              (CloseoutFinalC10ThresholdRows.listDenominator a r (targetDenominator r.q)),
        ∑ z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card,
          exactColumnCount (thrHolds r liveScale)
            (printedParityRow a r liveScale
              (CloseoutFinalC10ThresholdRows.listDenominator a r (targetDenominator r.q))
              sample.1.val (fun sel => thrOffset a r liveScale z sel sample.1.val) sample.2)
            z := by
  rw [acceptanceCount_unfold]
  rw [Fintype.sum_equiv
      ((finCongr (parityRows_rowCount spectrum theta a liveScale targetDenominator r)).trans
        (primeListSampleFinEquiv
          (cutoff := CloseoutFinalC10ThresholdRows.primeCutoff a r (targetDenominator r.q))
          (thresholdFourfoldOccurrences r) liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator a r (targetDenominator r.q))).symm)
      (fun index : Fin ((parityRows spectrum theta a liveScale targetDenominator).rowCount r) =>
        ∑ input : BitInput r.q,
          ((parityRows spectrum theta a liveScale targetDenominator).row r index input).toNat)
      (fun sample => ∑ input : BitInput r.q,
        (parityRow a r liveScale (targetDenominator r.q) input sample).toNat)
      (fun index => by
        refine Finset.sum_congr rfl (fun input _ => ?_)
        rw [parityRows_row]
        rfl)]
  apply Finset.sum_congr rfl
  intro sample _
  rw [← Equiv.sum_comp
    (normalizedLiveExternalInputEquiv
      (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)).symm
    (fun input : BitInput r.q =>
      (parityRow a r liveScale (targetDenominator r.q) input sample).toNat)]
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro z _
  rw [exactColumnCount_printedParityRow]
  rfl

end Bridge

end

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdParityRow
