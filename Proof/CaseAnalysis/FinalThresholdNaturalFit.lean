import Proof.CaseAnalysis.FinalThresholdNaturalSum

/-!
C10's natural THR/mixed numerator reuses the existing denominator envelope.
A.13.10 excludes the child population from the denominator. Accuracy bounds
the actual numerator by twice that denominator, so its already-reserved
extra bit suffices; no separate log-|G| width is required.
-/

open NearCubicWires NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalk
open NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalFit

open C10ThresholdNaturalSum C10UnionSupplier CloseoutFinalC10ThresholdRows

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The exact existing left sample population at the two-way reserve. -/
def leftRows (sources : EightSources) (liveScale target : ℕ) :=
  symmetricFourfoldRows (expanderOf sources) liveScale
    (fun _ => reciprocalUnionDenominator 1 target)

def numerator (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) : ℕ :=
  mixedNativeNumeratorOf (decompositionOf sources) (leftRows sources liveScale target)
    liveScale (reciprocalUnionDenominator 1 target) request

def denominator (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) : ℕ :=
  mixedNativeDenominatorOf (decompositionOf sources) (leftRows sources liveScale target)
    liveScale (reciprocalUnionDenominator 1 target) request

/-- Native mixed denominator equals the current union row denominator exactly. -/
theorem denominator_eq_rowDenominator (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) :
    denominator sources liveScale target request =
      rowDenominator (unionAtomRows sources liveScale (fun _ => target))
        request.q request.circuits := by
  unfold denominator mixedNativeDenominatorOf nativeDenominator rowDenominator
  rw [unionAtomRows_rowCount]
  rw [C10ThresholdRowIdentity.thresholdRows_rowCount]
  simp only [Fintype.card_prod, Nat.mul_assoc]
  rfl

theorem denominator_pos (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) :
    0 < denominator sources liveScale target request := by
  rw [denominator_eq_rowDenominator]
  exact rowDenominator_pos _ _ _

/-- The selected fraction matches the mixed rational estimator. -/
theorem ratio_eq (sources : EightSources) (liveScale target : ℕ)
    (request : FourfoldRequest DecodeUnion) :
    (numerator sources liveScale target request : ℚ) /
      denominator sources liveScale target request =
        mixedRatio (decompositionOf sources) (expanderOf sources) liveScale target request := rfl

/-- Positive requested accuracy makes the natural estimate strictly less than two. -/
theorem numerator_lt_twice_denominator (sources : EightSources) (liveScale target : ℕ)
    (htarget : 0 < target) (request : FourfoldRequest DecodeUnion) :
    numerator sources liveScale target request < 2 * denominator sources liveScale target request := by
  have herror := mixedRatio_error_le (decompositionOf sources) (expanderOf sources)
    (primeOf sources) liveScale target request
  have hprob : conjunctionProbability decodeUnionEvaluate request.circuits ≤ 1 :=
    booleanMean_le_one _
  have ht : (1 : ℝ) < (target + 1 : ℕ) := by exact_mod_cast Nat.succ_lt_succ htarget
  have he : (1 : ℝ) / (target + 1 : ℕ) < 1 :=
    (div_lt_one (by positivity)).2 ht
  have hratio : (mixedRatio (decompositionOf sources) (expanderOf sources)
      liveScale target request : ℝ) < 2 := by
    have hh := (abs_le.mp herror).2
    linarith
  rw [← ratio_eq sources liveScale target request] at hratio
  have hd : (0 : ℝ) < denominator sources liveScale target request := by
    exact_mod_cast denominator_pos sources liveScale target request
  have hn : (numerator sources liveScale target request : ℝ) <
      2 * denominator sources liveScale target request := by
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast] at hratio
    exact (div_lt_iff₀ hd).mp hratio
  exact_mod_cast hn

/-- Use the same extra bit already reserved for the denominator's envelope. -/
theorem numerator_lt_two_pow (sources : EightSources) (liveScale target bits : ℕ)
    (htarget : 0 < target) (request : FourfoldRequest DecodeUnion)
    (hden : denominator sources liveScale target request ≤ 2 ^ bits) :
    numerator sources liveScale target request < 2 ^ (bits + 1) := by
  apply (numerator_lt_twice_denominator sources liveScale target htarget request).trans_le
  simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 hden

/-- The actual external-row majorant feeds both numeric fits at the existing width. -/
theorem numerator_lt_two_pow_of_rowCount (sources : EightSources)
    (liveScale target seedBits width : ℕ) (htarget : 0 < target)
    (request : FourfoldRequest DecodeUnion)
    (hrows : (unionAtomRows sources liveScale (fun _ => target)).rowCount request ≤ 2 ^ seedBits)
    (hwidth : request.q + seedBits + 1 ≤ width) :
    numerator sources liveScale target request < 2 ^ width := by
  have hden : denominator sources liveScale target request ≤ 2 ^ (request.q + seedBits) := by
    rw [denominator_eq_rowDenominator]
    change (unionAtomRows sources liveScale (fun _ => target)).rowCount request * 2 ^ request.q ≤ _
    calc
      _ ≤ 2 ^ seedBits * 2 ^ request.q := Nat.mul_le_mul_right _ hrows
      _ = _ := by rw [← pow_add, Nat.add_comm]
  exact (numerator_lt_two_pow sources liveScale target (request.q + seedBits)
    htarget request hden).trans_le (Nat.pow_le_pow_right (by decide) hwidth)

/-- The stage's existing constant accuracy target is positive whenever its
coefficient-mass cap is nonnegative. This introduces no new accuracy choice. -/
theorem accuracyTargetAll_pos {source : PointwisePCPPAlgorithm}
    (constants : CompetitorRationalGap.Constants source)
    (limits : CanonicalWitnessCodec.LegalSumLimits) (hmass : 0 ≤ limits.coefficientMassCap) :
    0 < C10SupplierAccuracyChain.accuracyTargetAll constants limits := by
  have hm : (0 : ℚ) < C10FamilyMass.siteMassBound limits.coefficientMassCap .penalty := by
    dsimp [C10FamilyMass.siteMassBound]
    positivity
  have h := C10SupplierAccuracyChain.accuracyTarget_spec constants limits .penalty
    (C10SupplierAccuracyChain.accuracyTargetAll constants limits)
    (C10SupplierAccuracyChain.accuracyTarget_le_all constants limits .penalty)
  by_contra hn
  have hz : C10SupplierAccuracyChain.accuracyTargetAll constants limits = 0 :=
    Nat.eq_zero_of_not_pos hn
  rw [hz, Nat.cast_zero, zero_mul] at h
  have hp : (0 : ℝ) < 2 * (C10FamilyMass.siteMassBound limits.coefficientMassCap .penalty : ℚ) := by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℚ) < 2) hm)
  exact (not_le_of_gt hp) h

end
end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalFit
