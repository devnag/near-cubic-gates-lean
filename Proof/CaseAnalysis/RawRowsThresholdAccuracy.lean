import Proof.CaseAnalysis.RawRowsThresholdSize
import Proof.CaseAnalysis.RawRowsModeBounds

/-! The actual threshold family uses coarse source-fixed metadata. Its
selection SUM, prime normalization and two error reserves remain unchanged. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierPrime SourceInterfaces RepairRepresentation
open PolynomialSchedule RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def thresholdFamilyBound (a : DecompositionAlgorithm) (desc : ℕ) :=
  (sourceChildBound a desc+1)^4
def thresholdPrimeDen (a : DecompositionAlgorithm) (desc target : ℕ) :=
  reciprocalUnionDenominator (thresholdFamilyBound a desc) target
def thresholdCutoff (a : DecompositionAlgorithm) (desc target : ℕ) :=
  canonicalPrimeCutoff (thresholdMagnitudeExponent a desc) (thresholdPrimeDen a desc target)
def thresholdListDen (a : DecompositionAlgorithm) (desc target : ℕ) :=
  modulusDigitCount (thresholdCutoff a desc target)*(thresholdPrimeDen a desc target+1)

def thresholdPrimeCertificate (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4) (hd : ∀ c∈r.circuits,c.descriptionBits ≤ desc) :
    PrimeSurrogateCertificate (ThresholdRows.Selection a r)
      (PrimeIndex (thresholdCutoff a desc target)) (Fin (thresholdFourfoldOccurrences r).length → Bool) :=
  primeSurrogateCertificateFor theta (ThresholdRows.equation a r)
    (canonicalPrimeCutoff_ge_563 _ _) (actual_threshold_difference a r desc hfour hd)

theorem threshold_prime_error (theta : PrimeThetaBoundContract) (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4) (hd : ∀ c∈r.circuits,c.descriptionBits ≤ desc) :
    (thresholdPrimeCertificate theta a r desc target hfour hd).error ≤
      1/(thresholdPrimeDen a desc target+1 : ℕ) :=
  canonicalPrimeError_le _ _

theorem threshold_list_error (a : DecompositionAlgorithm) (desc target : ℕ)
    (prime : PrimeIndex (thresholdCutoff a desc target)) :
    (modulusDigitCount prime.val : ℝ)/(thresholdListDen a desc target+1 : ℕ) ≤
      1/(thresholdPrimeDen a desc target+1 : ℕ) := by
  have hp : modulusDigitCount prime.val ≤ modulusDigitCount (thresholdCutoff a desc target) :=
    PolynomialClock.natBitLength_mono (mem_primesUpTo.mp prime.property).2
  have hpos (n : ℕ) : (0 : ℝ) < (n+1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  rw [div_le_div_iff₀ (hpos _) (hpos _)]
  unfold thresholdListDen
  have hpR : (modulusDigitCount prime.val : ℝ) ≤ modulusDigitCount (thresholdCutoff a desc target) := by exact_mod_cast hp
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hpR
    (show (0 : ℝ) ≤ (thresholdPrimeDen a desc target : ℝ)+1 from
      add_nonneg (Nat.cast_nonneg _) zero_le_one)]

theorem threshold_union_error (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4) (hd : ∀ c∈r.circuits,c.descriptionBits ≤ desc)
    (primeError listError : ℝ)
    (hp : primeError ≤ 1/(thresholdPrimeDen a desc target+1 : ℕ))
    (hl : listError ≤ 1/(thresholdPrimeDen a desc target+1 : ℕ)) :
    (Fintype.card (ThresholdRows.Selection a r) : ℝ)*(primeError+listError) ≤ 1/(target+1 : ℕ) := by
  have hF : (Fintype.card (ThresholdRows.Selection a r) : ℝ) ≤ thresholdFamilyBound a desc := by
    exact_mod_cast selection_count a r desc hfour hd
  calc
    _ ≤ (Fintype.card (ThresholdRows.Selection a r) : ℝ)*
        (1/(thresholdPrimeDen a desc target+1 : ℕ)+1/(thresholdPrimeDen a desc target+1 : ℕ)) := by gcongr
    _ ≤ (thresholdFamilyBound a desc : ℝ)*
        (1/(thresholdPrimeDen a desc target+1 : ℕ)+1/(thresholdPrimeDen a desc target+1 : ℕ)) :=
      mul_le_mul_of_nonneg_right hF (by positivity)
    _ ≤ _ := reciprocalUnionBudget _ _

theorem threshold_parameters_polynomial (a : DecompositionAlgorithm) (degree : ℕ)
    (target : ℕ → ℕ) (ht : PolynomiallyBounded target) :
    PolynomiallyBounded (fun q=>thresholdPrimeDen a (descriptionEnvelope degree q) (target q)) ∧
    PolynomiallyBounded (fun q=>thresholdCutoff a (descriptionEnvelope degree q) (target q)) ∧
    PolynomiallyBounded (fun q=>thresholdListDen a (descriptionEnvelope degree q) (target q)) := by
  have h1 := polynomiallyBounded_constant 1
  have hF := polynomiallyBounded_pow (polynomiallyBounded_add
    (sourceChildBound_polynomial a (descriptionEnvelope_polynomial degree)) h1) 4
  have hden := polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hF)
    (polynomiallyBounded_add ht h1)
  have hcut := primeCutoff_polynomial (thresholdMagnitudeExponent_polynomial a degree) hden
  refine ⟨hden,hcut,?_⟩
  exact polynomiallyBounded_mul (CloseoutWitnessResources.bits_polynomial hcut)
    (polynomiallyBounded_add hden h1)

theorem threshold_mode_logs (a : DecompositionAlgorithm) (degree : ℕ)
    (target : ℕ → ℕ) (ht : PolynomiallyBounded target) :
    ∃ cz ct : ℕ, 0 < cz ∧ 0 < ct ∧ ∀ q,
      SupplierWalkBridge.canonicalWalkLength (thresholdListDen a (descriptionEnvelope degree q) (target q))+1 ≤ ct*logScale q ∧
      ∀ prime : PrimeIndex (thresholdCutoff a (descriptionEnvelope degree q) (target q)),
        modulusDigitCount prime.val+1 ≤ cz*logScale q := by
  obtain ⟨_,hcut,hden⟩ := threshold_parameters_polynomial a degree target ht
  obtain ⟨cz,hcz,hz⟩ := polynomial_prime_digits_log hcut
  obtain ⟨ct,hct,hw⟩ := polynomial_walk_log hden
  exact ⟨cz,ct,hcz,hct,fun q=>⟨hw q,hz q⟩⟩

end
end NearCubicWires.RepairSource.CloseoutRawRows
