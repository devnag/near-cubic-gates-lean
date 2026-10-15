import Proof.CaseAnalysis.FinalThresholdParityRow
import Proof.CaseAnalysis.FinalUnionSupplier

/-!
A.13.10: the natural sum of the separate fixed `(g,p,e,f)` table counts.
The scalar offset is selected from the residual column; it is not a vector
of offsets hidden inside a polynomial. The child label stays outside GF(2).
This module supplies local value/error adapters, not a physical supplier run.
Resource owner: A.8 and A.13.8; per-g printing retains the existing row fit.
-/

open NearCubicWires NearCubicWires.RepairSource
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierWalk NearCubicWires.SupplierRadix
open NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.CloseoutRawRows

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalSum

open C10PrinterBridge C10ThresholdParityRow

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-- One per-g printed row, with exactly the scalar offset selected by z. -/
theorem exactPolynomialValue_thresholdRow (liveScale listDen : ℕ) {cutoff : ℕ}
    (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen)
    (y : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card) :
    exactPolynomialValue (C10ThresholdParityRow.thrHolds r liveScale)
        (thresholdRow a r sel liveScale listDen prime.val
          (C10ThresholdParityRow.thrOffset a r liveScale z sel prime.val) seed) y z =
      CloseoutFinalC10ThresholdRows.selectionRow a r liveScale listDen
        (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z)
        sel prime seed := by
  rw [← C10ThresholdParityRow.thrOffset_spec a r liveScale y z sel prime.val,
    ← C10PrinterBridge.evaluateStructuralGF2_eq_exactPolynomialValue]
  exact C10ThresholdRowIdentity.thresholdRow_eq_selectionRow a r liveScale listDen
    (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z)
    sel prime seed

/-- The paper's T[g,p,e,f](z), before the natural outer sum over g. -/
theorem exactColumnCount_thresholdRow (liveScale listDen : ℕ) {cutoff : ℕ}
    (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card) :
    exactColumnCount (C10ThresholdParityRow.thrHolds r liveScale)
        (thresholdRow a r sel liveScale listDen prime.val
          (C10ThresholdParityRow.thrOffset a r liveScale z sel prime.val) seed) z =
      ∑ y : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card,
        (CloseoutFinalC10ThresholdRows.selectionRow a r liveScale listDen
          (splitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) y z)
          sel prime seed).toNat := by
  unfold exactColumnCount
  exact Finset.sum_congr rfl (fun y _ => congrArg Bool.toNat
    (exactPolynomialValue_thresholdRow a r liveScale listDen sel prime seed y z))

/-- The natural numerator. The child index is summed, not normalized. -/
def nativeNumerator (liveScale listDen cutoff : ℕ) : ℕ :=
  ∑ sel : ThresholdRows.Selection a r, ∑ prime : PrimeIndex cutoff,
    ∑ seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen,
      ∑ input : BitInput r.q,
        (CloseoutFinalC10ThresholdRows.selectionRow a r liveScale listDen input
          sel prime seed).toNat

/-- The paper's denominator excludes the child population. -/
def nativeDenominator (liveScale listDen cutoff : ℕ) : ℕ :=
  Fintype.card (PrimeIndex cutoff) *
    Fintype.card (NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen) *
      2 ^ r.q

/-- Natural summation of separate printed tables is the native numerator. -/
theorem nativeNumerator_eq_tableSum (liveScale listDen cutoff : ℕ) :
    nativeNumerator a r liveScale listDen cutoff =
      ∑ sel : ThresholdRows.Selection a r, ∑ prime : PrimeIndex cutoff,
        ∑ seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen,
          ∑ z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card,
            exactColumnCount (C10ThresholdParityRow.thrHolds r liveScale)
              (thresholdRow a r sel liveScale listDen prime.val
                (C10ThresholdParityRow.thrOffset a r liveScale z sel prime.val) seed) z := by
  unfold nativeNumerator
  apply Finset.sum_congr rfl
  intro sel _
  apply Finset.sum_congr rfl
  intro prime _
  apply Finset.sum_congr rfl
  intro seed _
  rw [← Equiv.sum_comp
    (normalizedLiveExternalInputEquiv
      (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)).symm
    (fun input : BitInput r.q =>
      (CloseoutFinalC10ThresholdRows.selectionRow a r liveScale listDen input
        sel prime seed).toNat)]
  rw [Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl (fun z _ =>
    (exactColumnCount_thresholdRow a r liveScale listDen sel prime seed z).symm)

/-- A natural child sum needs only the child-count factor in its bit bound. -/
theorem nativeNumerator_le (liveScale listDen cutoff : ℕ) :
    nativeNumerator a r liveScale listDen cutoff ≤
      Fintype.card (ThresholdRows.Selection a r) *
        nativeDenominator r liveScale listDen cutoff := by
  unfold nativeNumerator nativeDenominator
  calc
    _ ≤ ∑ _sel : ThresholdRows.Selection a r, ∑ _prime : PrimeIndex cutoff,
          ∑ _seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen,
            ∑ _input : BitInput r.q, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro sel _
      apply Finset.sum_le_sum
      intro prime _
      apply Finset.sum_le_sum
      intro seed _
      apply Finset.sum_le_sum
      intro input _
      cases CloseoutFinalC10ThresholdRows.selectionRow a r liveScale listDen input
        sel prime seed <;> decide
    _ = _ := by simp [mul_assoc]

/-- Short arithmetic seam for a Boolean left estimator and a natural THR mean. -/
theorem mixed_mean_error (leftMean rightMean : ℝ) (leftTarget rightTarget : Bool)
    (hleft0 : 0 ≤ leftMean) (hleft1 : leftMean ≤ 1) :
    |leftMean * rightMean - bitAsReal leftTarget * bitAsReal rightTarget| ≤
      |rightMean - bitAsReal rightTarget| + |leftMean - bitAsReal leftTarget| := by
  have ht : |bitAsReal rightTarget| ≤ 1 := by
    cases rightTarget <;> norm_num [bitAsReal]
  calc
    _ = |leftMean * (rightMean - bitAsReal rightTarget) +
          bitAsReal rightTarget * (leftMean - bitAsReal leftTarget)| := by
      congr 1
      ring
    _ ≤ |leftMean * (rightMean - bitAsReal rightTarget)| +
          |bitAsReal rightTarget * (leftMean - bitAsReal leftTarget)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hleft0, abs_mul]
      exact add_le_add
        (by simpa using (mul_le_mul_of_nonneg_right hleft1
          (abs_nonneg (rightMean - bitAsReal rightTarget))))
        (by simpa using (mul_le_mul_of_nonneg_right ht
          (abs_nonneg (leftMean - bitAsReal leftTarget))))

/-- A prime surrogate's two Boolean cases give its mismatch bound. -/
theorem prime_mismatch_le {Equation Prime Input : Type} [Fintype Prime]
    (c : PrimeSurrogateCertificate Equation Prime Input) (equation : Equation) (input : Input) :
    booleanMean (fun prime => c.modular equation prime input != c.exact equation input) ≤
      c.error := by
  cases he : c.exact equation input with
  | false => simpa [he] using c.sound equation input (by simp [he])
  | true =>
    have hm : ∀ prime, c.modular equation prime input = true :=
      fun prime => c.complete equation input (by simp [he]) prime
    simpa [booleanMean, he, hm, bitAsReal] using c.errorNonnegative

/-- Absolute error of a Boolean average is bounded by its mismatch frequency. -/
theorem booleanMean_error_le {Sample : Type} [Fintype Sample]
    (hcard : 0 < Fintype.card Sample) (row : Sample → Bool) (target : Bool) :
    |booleanMean row - bitAsReal target| ≤ booleanMean (fun sample => row sample != target) := by
  have hc : (0 : ℝ) < Fintype.card Sample := by exact_mod_cast hcard
  have ht : bitAsReal target = (∑ _ : Sample, bitAsReal target) / Fintype.card Sample := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [ht]
  unfold booleanMean
  rw [← sub_div, abs_div, abs_of_pos hc, ← Finset.sum_sub_distrib]
  apply div_le_div_of_nonneg_right _ hc.le
  calc
    _ ≤ ∑ sample, |bitAsReal (row sample) - bitAsReal target| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl (fun sample _ => bitAsReal_sub_abs_eq_mismatch _ _)

open CloseoutFinalC10ThresholdRows

/-- One fixed child tuple's prime/list mismatch, at the existing two-part reserve. -/
theorem selection_mismatch_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ) (input : BitInput r.q)
    (sel : ThresholdRows.Selection a r) :
    booleanMean
      (fun sample : PrimeIndex (primeCutoff a r target) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (listDenominator a r target) =>
        selectionRow a r liveScale (listDenominator a r target) input sel sample.1 sample.2 !=
          exactRow a r sel input) ≤
      1 / (primeDenominator a r target + 1 : ℕ) +
        1 / (primeDenominator a r target + 1 : ℕ) := by
  have hp := (certificate theta a r target).cardPositive
  have he := (normalizedOccurrenceListCertificate spectrum (thresholdFourfoldOccurrences r)
    liveScale (listDenominator a r target)).cardPositive
  let actual : Fin (thresholdFourfoldOccurrences r).length → Bool :=
    fun index => ((thresholdFourfoldOccurrences r).get index).eval input
  have hlist : booleanMean
      (fun sample : PrimeIndex (primeCutoff a r target) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (listDenominator a r target) =>
        selectionRow a r liveScale (listDenominator a r target) input sel sample.1 sample.2 !=
          modularEquationHolds (ThresholdRows.equation a r sel) sample.1 actual) ≤
        1 / (primeDenominator a r target + 1 : ℕ) := by
    apply booleanMean_product_le_of_fiber _ _ hp he
    intro prime
    calc
      _ ≤ (modulusDigitCount prime.val : ℝ) / (listDenominator a r target + 1 : ℕ) :=
        selectionRow_mismatch_reciprocal spectrum a r liveScale
          (listDenominator a r target) input sel prime
      _ ≤ (modulusDigitCount (primeCutoff a r target) : ℝ) /
          (listDenominator a r target + 1 : ℕ) := by
        gcongr
        exact_mod_cast Nat.succ_le_succ
          (Nat.log_mono_right (mem_primesUpTo.mp prime.property).2)
      _ ≤ _ := listUnionError_le a r target
  have hprime : booleanMean
      (fun sample : PrimeIndex (primeCutoff a r target) ×
          NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
            (listDenominator a r target) =>
        modularEquationHolds (ThresholdRows.equation a r sel) sample.1 actual !=
          exactRow a r sel input) ≤ 1 / (primeDenominator a r target + 1 : ℕ) := by
    rw [booleanMean_product_left
      (fun prime : PrimeIndex (primeCutoff a r target) =>
        modularEquationHolds (ThresholdRows.equation a r sel) prime actual !=
          exactRow a r sel input) hp he]
    exact (prime_mismatch_le (certificate theta a r target) sel actual).trans
      (certificate_error_le theta a r target)
  exact (booleanMean_mismatch_triangle
    (fun sample : PrimeIndex (primeCutoff a r target) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r target) =>
      selectionRow a r liveScale (listDenominator a r target) input sel sample.1 sample.2)
    (fun sample => modularEquationHolds (ThresholdRows.equation a r sel) sample.1 actual)
    (fun _ => exactRow a r sel input)).trans (add_le_add hlist hprime)

/-- Natural child mean at one input; the existing reserve pays the sum over g. -/
def pointEstimate (liveScale target : ℕ) (input : BitInput r.q) : ℝ :=
  ∑ sel : ThresholdRows.Selection a r,
    booleanMean (fun sample : PrimeIndex (primeCutoff a r target) ×
        NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
          (listDenominator a r target) =>
      selectionRow a r liveScale (listDenominator a r target) input sel sample.1 sample.2)

/-- The natural per-input estimate has the paper's prescribed total error. -/
theorem pointEstimate_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ) (input : BitInput r.q) :
    |pointEstimate a r liveScale target input -
        bitAsReal (conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input)| ≤
      1 / (target + 1 : ℕ) := by
  have he := (normalizedOccurrenceListCertificate spectrum (thresholdFourfoldOccurrences r)
    liveScale (listDenominator a r target)).cardPositive
  have hp := (certificate theta a r target).cardPositive
  have hcard : 0 < Fintype.card (PrimeIndex (primeCutoff a r target) ×
      NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
        (listDenominator a r target)) := by
    rw [Fintype.card_prod]
    exact Nat.mul_pos hp he
  have hexact : (∑ sel : ThresholdRows.Selection a r, bitAsReal (exactRow a r sel input)) =
      bitAsReal (conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits input) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (exactRow_sum a r input)
    push_cast at h
    simpa only [SupplierList.bitAsReal_eq_toNat] using h
  rw [← hexact]
  unfold pointEstimate
  exact (sum_pointwise_error _ _
    (1 / (primeDenominator a r target + 1 : ℕ) +
      1 / (primeDenominator a r target + 1 : ℕ))
    (fun sel => (booleanMean_error_le hcard _ (exactRow a r sel input)).trans
      (selection_mismatch_le a r spectrum theta liveScale target input sel))).trans
    (reciprocalUnionBudget (Fintype.card (ThresholdRows.Selection a r)) target)

/-- Finite averaging preserves a uniform local absolute error. -/
theorem realMean_error_le {Input : Type} [Fintype Input] [Nonempty Input]
    (approximate exact : Input → ℝ) (error : ℝ)
    (herror : ∀ input, |approximate input - exact input| ≤ error) :
    |SupplierList.realMean approximate - SupplierList.realMean exact| ≤ error := by
  have hc : (0 : ℝ) < Fintype.card Input := by exact_mod_cast Fintype.card_pos
  unfold SupplierList.realMean
  rw [← sub_div, abs_div, abs_of_pos hc]
  apply (div_le_iff₀ hc).2
  exact (sum_pointwise_error exact approximate error herror).trans_eq (mul_comm _ _)

/-- The natural THR estimator, averaged over actual inputs. -/
def estimate (liveScale target : ℕ) : ℝ :=
  SupplierList.realMean (pointEstimate a r liveScale target)

theorem estimate_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ) :
    |estimate a r liveScale target -
        conjunctionProbability NormalizedThresholdThresholdCircuit.eval r.circuits| ≤
      1 / (target + 1 : ℕ) :=
  realMean_error_le _ _ _ (pointEstimate_error_le a r spectrum theta liveScale target)

/-- The averaged natural estimator is exactly the ratio of the native integers. -/
theorem estimate_eq_ratio (liveScale target : ℕ) :
    estimate a r liveScale target =
      (nativeNumerator a r liveScale (listDenominator a r target) (primeCutoff a r target) : ℝ) /
        nativeDenominator r liveScale (listDenominator a r target) (primeCutoff a r target) := by
  unfold estimate SupplierList.realMean pointEstimate booleanMean
    nativeNumerator nativeDenominator
  simp only [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul, Nat.cast_sum,
    SupplierList.bitAsReal_eq_toNat, ← Finset.sum_div, div_div]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sel _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro prime _
  rw [Finset.sum_comm]

/-- Natural numerator at one input, used by the mixed-atom value adapter. -/
def pointNumerator (liveScale listDen cutoff : ℕ) (input : BitInput r.q) : ℕ :=
  ∑ sel : ThresholdRows.Selection a r, ∑ prime : PrimeIndex cutoff,
    ∑ seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen,
      (selectionRow a r liveScale listDen input sel prime seed).toNat

theorem pointEstimate_eq_ratio (liveScale target : ℕ) (input : BitInput r.q) :
    pointEstimate a r liveScale target input =
      (pointNumerator a r liveScale (listDenominator a r target)
        (primeCutoff a r target) input : ℝ) /
      (Fintype.card (PrimeIndex (primeCutoff a r target)) *
        Fintype.card (NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r)
          liveScale (listDenominator a r target)) : ℕ) := by
  unfold pointEstimate pointNumerator booleanMean
  simp only [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_sum,
    SupplierList.bitAsReal_eq_toNat, Finset.sum_div]

open C10UnionSupplier

/-- Mixed input mean with an explicit symmetric/parity row producer. -/
def mixedPointEstimateOf
    (rows : FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval)
    (liveScale target : ℕ) (request : FourfoldRequest DecodeUnion)
    (input : BitInput request.q) : ℝ :=
  booleanMean (fun index => rows.row (leftRequest request) index input) *
    pointEstimate a (rightRequest request) liveScale target input

/-- Abstract the existing left row object so elaboration never unfolds its large
construction while checking the small product-error step. -/
theorem mixedPointEstimateOf_error_le
    (rows : FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval)
    (spectrum : ExpanderSpectrumContract) (theta : PrimeThetaBoundContract)
    (liveScale target : ℕ) (request : FourfoldRequest DecodeUnion)
    (input : BitInput request.q) :
    |mixedPointEstimateOf a rows liveScale target request input -
        bitAsReal (conjunctionBit decodeUnionEvaluate request.circuits input)| ≤
      1 / (target + 1 : ℕ) + rows.failure (leftRequest request) := by
  let leftMean := booleanMean (fun index => rows.row (leftRequest request) index input)
  let rightMean := pointEstimate a (rightRequest request) liveScale target input
  let leftTarget := conjunctionBit NormalizedSymmetricThresholdCircuit.eval
    (leftRequest request).circuits input
  let rightTarget := conjunctionBit NormalizedThresholdThresholdCircuit.eval
    (rightRequest request).circuits input
  have hl0 : 0 ≤ leftMean := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun index _ => SupplierWalk.bitAsReal_nonnegative _)
  have hl1 : leftMean ≤ 1 := booleanMean_le_one _
  have hl : |leftMean - bitAsReal leftTarget| ≤ rows.failure (leftRequest request) :=
    (booleanMean_error_le
      (Sample := Fin (rows.rowCount (leftRequest request)))
      (by simpa using rows.rowCountPositive (leftRequest request)) _ _).trans
      (rows.pointwise (leftRequest request) input)
  have hr : |rightMean - bitAsReal rightTarget| ≤ 1 / (target + 1 : ℕ) :=
    pointEstimate_error_le a (rightRequest request) spectrum theta liveScale target input
  have ht : bitAsReal (conjunctionBit decodeUnionEvaluate request.circuits input) =
      bitAsReal leftTarget * bitAsReal rightTarget := by
    rw [conjunctionBit_union NormalizedSymmetricThresholdCircuit.eval
      NormalizedThresholdThresholdCircuit.eval request.circuits input]
    change bitAsReal (leftTarget && rightTarget) = _
    cases leftTarget <;> cases rightTarget <;> norm_num [bitAsReal]
  rw [ht]
  exact (mixed_mean_error leftMean rightMean leftTarget rightTarget hl0 hl1).trans
    (add_le_add hr hl)

/-- Actual mixed request at the two-way constant reserve. -/
def mixedPointEstimate (spectrum : ExpanderSpectrumContract) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) (input : BitInput request.q) : ℝ :=
  mixedPointEstimateOf a
    (symmetricFourfoldRows spectrum liveScale (fun _ => reciprocalUnionDenominator 1 target))
    liveScale (reciprocalUnionDenominator 1 target) request input

theorem mixedPointEstimate_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) (input : BitInput request.q) :
    |mixedPointEstimate a spectrum liveScale target request input -
        bitAsReal (conjunctionBit decodeUnionEvaluate request.circuits input)| ≤
      1 / (target + 1 : ℕ) := by
  have h := mixedPointEstimateOf_error_le a
    (symmetricFourfoldRows spectrum liveScale (fun _ => reciprocalUnionDenominator 1 target))
    spectrum theta liveScale (reciprocalUnionDenominator 1 target) request input
  apply h.trans
  change (1 : ℝ) / (reciprocalUnionDenominator 1 target + 1 : ℕ) +
    1 / (reciprocalUnionDenominator 1 target + 1 : ℕ) ≤ 1 / (target + 1 : ℕ)
  simpa using reciprocalUnionBudget 1 target

/-- The actual mixed-list probability, including systematic parity atoms through
atomToUnion, has the same prescribed accuracy. -/
theorem mixedEstimate_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) :
    |SupplierList.realMean (mixedPointEstimate a spectrum liveScale target request) -
        conjunctionProbability decodeUnionEvaluate request.circuits| ≤
      1 / (target + 1 : ℕ) :=
  realMean_error_le _ _ _
    (mixedPointEstimate_error_le a spectrum theta liveScale target request)

/-- Mixed numerator: finite counts at the same input, with g summed naturally. -/
def mixedNativeNumeratorOf
    (rows : FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval)
    (liveScale target : ℕ) (request : FourfoldRequest DecodeUnion) : ℕ :=
  ∑ input : BitInput request.q,
    (∑ index : Fin (rows.rowCount (leftRequest request)),
      (rows.row (leftRequest request) index input).toNat) *
      pointNumerator a (rightRequest request) liveScale
        (listDenominator a (rightRequest request) target)
        (primeCutoff a (rightRequest request) target) input

/-- The independent sample populations are normalized; the child population is not. -/
def mixedNativeDenominatorOf
    (rows : FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval)
    (liveScale target : ℕ) (request : FourfoldRequest DecodeUnion) : ℕ :=
  rows.rowCount (leftRequest request) * nativeDenominator (rightRequest request)
    liveScale (listDenominator a (rightRequest request) target)
    (primeCutoff a (rightRequest request) target)

/-- Exact rational realization of the mixed semantic estimate. -/
theorem mixedEstimateOf_eq_ratio
    (rows : FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval)
    (liveScale target : ℕ) (request : FourfoldRequest DecodeUnion) :
    SupplierList.realMean (mixedPointEstimateOf a rows liveScale target request) =
      (mixedNativeNumeratorOf a rows liveScale target request : ℝ) /
        mixedNativeDenominatorOf a rows liveScale target request := by
  unfold SupplierList.realMean mixedPointEstimateOf
  simp_rw [pointEstimate_eq_ratio]
  unfold booleanMean mixedNativeNumeratorOf mixedNativeDenominatorOf nativeDenominator
  simp only [SupplierList.bitAsReal_eq_toNat, Nat.cast_sum, Nat.cast_mul,
    div_mul_div_comm, ← Finset.sum_div, div_div,
    Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
  rfl

/-- The actual source-selected mixed rational supplier. -/
def mixedRatio (spectrum : ExpanderSpectrumContract) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) : ℚ :=
  let rows := symmetricFourfoldRows spectrum liveScale
    (fun _ => reciprocalUnionDenominator 1 target)
  (mixedNativeNumeratorOf a rows liveScale (reciprocalUnionDenominator 1 target) request : ℚ) /
    mixedNativeDenominatorOf a rows liveScale (reciprocalUnionDenominator 1 target) request

theorem mixedRatio_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) :
    |(mixedRatio a spectrum liveScale target request : ℝ) -
        conjunctionProbability decodeUnionEvaluate request.circuits| ≤
      1 / (target + 1 : ℕ) := by
  unfold mixedRatio
  push_cast
  rw [← mixedEstimateOf_eq_ratio]
  have h := mixedEstimate_error_le a spectrum theta liveScale target request
  unfold mixedPointEstimate at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Immediate mixed C10 atom consumer, preserving the existing systematic parity bridge. -/
theorem mixedRatio_atoms_error_le (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract) (liveScale target : ℕ)
    {N : ℕ} {circuit : BooleanCircuit N} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) :
    |(mixedRatio a spectrum liveScale target ⟨N, atoms.map atomToUnion⟩ : ℝ) -
        conjunctionProbability C10TotalDecode.evaluate atoms| ≤ 1 / (target + 1 : ℕ) := by
  rw [← conjunctionProbability_atomToUnion atoms]
  exact mixedRatio_error_le a spectrum theta liveScale target ⟨N, atoms.map atomToUnion⟩

end
end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalSum
