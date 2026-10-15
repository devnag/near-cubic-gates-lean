import Proof.MachineModel.CanonicalFourfoldRowTailProgram
import Proof.MachineModel.FixedAccuracyDenominatorProgram

/-!
# The published row counts as closed natural-number arithmetic

The row-major atom count consumed by the aggregation front end is
`rows.rowCount request * 2 ^ request.q`, and
`CanonicalFourfoldRowCountProgram` already executes the second factor and the
product.  The first factor is a `Fintype.card` of a dependent walk-sample
type, which no machine can evaluate directly.

This module removes that obstacle *before* any counting program is written:
it replaces both published row counts by explicit natural-number arithmetic in
the request's own data.  Nothing here is executable and nothing here is
asymptotic; every equality is an exact cardinality identity.

After this reduction the counting residual is purely numeric — a base-two
ceiling logarithm, the occurrence population, the touching cost, and (in the
threshold family) the prime-window cardinality.
-/

namespace NearCubicWires.CanonicalFourfoldRowCountFormula

open NearCubicWires
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierTouching
open NearCubicWires.SupplierWalk
open NearCubicWires.SupplierWalkBridge

/-! ## §1 The canonical walk-sample cardinality -/

/-- Vertex universe of the canonical padded Margulis walk. -/
private theorem card_margulisVertex_two_pow (side : ℕ) :
    Fintype.card (MargulisVertex (2 ^ side)) = 2 ^ (2 * side) := by
  rw [show Fintype.card (MargulisVertex (2 ^ side)) =
      Fintype.card (ZMod (2 ^ side)) * Fintype.card (ZMod (2 ^ side)) from
    Fintype.card_prod _ _]
  rw [ZMod.card]
  rw [two_mul, pow_add]

/-- **The occurrence-list seed count, in closed form.**  Every published
symmetric row index is one canonical Margulis transcript, so the row count is
a product of two explicit powers. -/
theorem card_normalizedOccurrenceListSeed
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    Fintype.card
        (NormalizedOccurrenceListSeed occurrences liveScale denominator) =
      2 ^ (2 * toeplitzWalkSideBits
          (canonicalGradedRank occurrences.length
            (touchingCost (occurrenceSupport occurrences)
              (normalizedLiveSet occurrences liveScale)))) *
        (16 ^ 40) ^ (2 * Nat.clog 2 (denominator + 1)) := by
  have hcard :
      Fintype.card
          (NormalizedOccurrenceListSeed occurrences liveScale denominator) =
        Fintype.card
            (MargulisVertex
              (2 ^ toeplitzWalkSideBits
                (canonicalGradedRank occurrences.length
                  (touchingCost (occurrenceSupport occurrences)
                    (normalizedLiveSet occurrences liveScale))))) *
          Fintype.card PoweredMargulisLabel ^
            (2 * Nat.clog 2 (denominator + 1)) :=
    card_positiveSample
  rw [hcard, card_margulisVertex_two_pow, card_poweredMargulisLabel]

/-! ## §2 The two published row counts -/

/-- Population and touching cost of the symmetric occurrence pool: the two
request-derived quantities that select the walk's vertex universe. -/
def symmetricOccurrencePopulation
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  (symmetricFourfoldOccurrences request).length

def symmetricOccurrenceTouchingCost
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) : ℕ :=
  touchingCost (occurrenceSupport (symmetricFourfoldOccurrences request))
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)

def thresholdOccurrencePopulation
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) : ℕ :=
  (thresholdFourfoldOccurrences request).length

def thresholdOccurrenceTouchingCost
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale : ℕ) : ℕ :=
  touchingCost (occurrenceSupport (thresholdFourfoldOccurrences request))
    (normalizedLiveSet (thresholdFourfoldOccurrences request) liveScale)

set_option maxHeartbeats 1600000 in
-- Unfolding the published preprocessor through its extensional row
-- replacement is kernel-heavy; the row-count field itself is definitional.
/-- **The published symmetric row count, in closed form.** -/
theorem publishedSymmetricRows_rowCount
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (publishedSymmetricRows contracts liveScale accuracyExponent).rowCount
        request =
      2 ^ (2 * toeplitzWalkSideBits
          (canonicalGradedRank (symmetricOccurrencePopulation request)
            (symmetricOccurrenceTouchingCost request liveScale))) *
        (16 ^ 40) ^ (2 * Nat.clog 2
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q) + 1)) := by
  have hfield :
      (publishedSymmetricRows contracts liveScale accuracyExponent).rowCount
          request =
        Fintype.card
          (NormalizedOccurrenceListSeed
            (symmetricFourfoldOccurrences request) liveScale
            (symmetricListDenominator request
              (fixedTargetDenominator accuracyExponent request.q))) :=
    rfl
  rw [hfield]
  exact card_normalizedOccurrenceListSeed (symmetricFourfoldOccurrences request)
    liveScale
    (symmetricListDenominator request
      (fixedTargetDenominator accuracyExponent request.q))

set_option maxHeartbeats 1600000 in
-- Same definitional unfolding as the symmetric case, through the dependent
-- prime/list replacement.
/-- **The published threshold row count, in closed form.**  The prime factor
is the cardinality of the canonical prime window. -/
theorem publishedThresholdRows_rowCount
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (publishedThresholdRows contracts liveScale accuracyExponent).rowCount
        request =
      (primesUpTo
          (thresholdPrimeCutoff (selectedExactDecompositionAlgorithm contracts)
            request
            (thresholdPrimeUnionDenominator
              (selectedExactDecompositionAlgorithm contracts) request
              (fixedTargetDenominator accuracyExponent request.q)))).card *
        (2 ^ (2 * toeplitzWalkSideBits
            (canonicalGradedRank (thresholdOccurrencePopulation request)
              (thresholdOccurrenceTouchingCost request liveScale))) *
          (16 ^ 40) ^ (2 * Nat.clog 2
            (thresholdListUnionDenominator
              (selectedExactDecompositionAlgorithm contracts) request
              (fixedTargetDenominator accuracyExponent request.q) + 1))) := by
  have hfield :
      (publishedThresholdRows contracts liveScale accuracyExponent).rowCount
          request =
        Fintype.card
          (PrimeIndex
              (thresholdPrimeCutoff
                (selectedExactDecompositionAlgorithm contracts) request
                (thresholdPrimeUnionDenominator
                  (selectedExactDecompositionAlgorithm contracts) request
                  (fixedTargetDenominator accuracyExponent request.q))) ×
            NormalizedOccurrenceListSeed
              (thresholdFourfoldOccurrences request) liveScale
              (thresholdListUnionDenominator
                (selectedExactDecompositionAlgorithm contracts) request
                (fixedTargetDenominator accuracyExponent request.q))) :=
    rfl
  rw [hfield, Fintype.card_prod, Fintype.card_coe]
  rw [card_normalizedOccurrenceListSeed (thresholdFourfoldOccurrences request)
    liveScale
    (thresholdListUnionDenominator
      (selectedExactDecompositionAlgorithm contracts) request
      (fixedTargetDenominator accuracyExponent request.q))]
  rfl

/-! ## §3 Collapsing both factors to one dyadic exponent

The powered Margulis label alphabet has size `16 ^ 40 = 2 ^ 160`, so the whole
symmetric row count is a *single* power of two.  This is the shape an
executable counter can reach with one dyadic exponential: the residual becomes
an exponent, not a cardinality. -/

private theorem poweredLabel_two_pow (exponent : ℕ) :
    ((16 : ℕ) ^ 40) ^ exponent = 2 ^ (160 * exponent) := by
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul]
  ring

private theorem two_pow_exponent_normalize (side walk : ℕ) :
    2 ^ (2 * side + 160 * (2 * walk)) = 2 ^ (2 * side + 320 * walk) := by
  congr 1
  ring

/-- The canonical dyadic exponent of one occurrence-list seed family. -/
def normalizedOccurrenceListSeedExponent
    (population activeBound denominator : ℕ) : ℕ :=
  2 * toeplitzWalkSideBits (canonicalGradedRank population activeBound) +
    320 * Nat.clog 2 (denominator + 1)

theorem card_normalizedOccurrenceListSeed_two_pow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    Fintype.card
        (NormalizedOccurrenceListSeed occurrences liveScale denominator) =
      2 ^ normalizedOccurrenceListSeedExponent occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale))
        denominator := by
  unfold normalizedOccurrenceListSeedExponent
  rw [card_normalizedOccurrenceListSeed, poweredLabel_two_pow, ← pow_add,
    two_pow_exponent_normalize]

/-- **The published symmetric row count is one power of two.** -/
theorem publishedSymmetricRows_rowCount_two_pow
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (publishedSymmetricRows contracts liveScale accuracyExponent).rowCount
        request =
      2 ^ normalizedOccurrenceListSeedExponent
        (symmetricOccurrencePopulation request)
        (symmetricOccurrenceTouchingCost request liveScale)
        (symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q)) := by
  unfold normalizedOccurrenceListSeedExponent
  rw [publishedSymmetricRows_rowCount, poweredLabel_two_pow, ← pow_add,
    two_pow_exponent_normalize]

/-- **The published threshold row count is a prime window times one power of
two.** -/
theorem publishedThresholdRows_rowCount_two_pow
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (publishedThresholdRows contracts liveScale accuracyExponent).rowCount
        request =
      (primesUpTo
          (thresholdPrimeCutoff (selectedExactDecompositionAlgorithm contracts)
            request
            (thresholdPrimeUnionDenominator
              (selectedExactDecompositionAlgorithm contracts) request
              (fixedTargetDenominator accuracyExponent request.q)))).card *
        2 ^ normalizedOccurrenceListSeedExponent
          (thresholdOccurrencePopulation request)
          (thresholdOccurrenceTouchingCost request liveScale)
          (thresholdListUnionDenominator
            (selectedExactDecompositionAlgorithm contracts) request
            (fixedTargetDenominator accuracyExponent request.q)) := by
  unfold normalizedOccurrenceListSeedExponent
  rw [publishedThresholdRows_rowCount, poweredLabel_two_pow, ← pow_add,
    two_pow_exponent_normalize]

/-! ## §4 The two published atom counts -/

/-- **The symmetric atom count, in closed form.**  This is the exact value the
front end's link-time counter must return. -/
theorem symmetricFourfoldRangeAtomCount_eq
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    FourfoldRangeAggregationComposition.fourfoldRangeAtomCount
        (publishedSymmetricRows contracts liveScale accuracyExponent)
        request =
      2 ^ (2 * toeplitzWalkSideBits
          (canonicalGradedRank (symmetricOccurrencePopulation request)
            (symmetricOccurrenceTouchingCost request liveScale))) *
        (16 ^ 40) ^ (2 * Nat.clog 2
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q) + 1)) *
        2 ^ request.q := by
  unfold FourfoldRangeAggregationComposition.fourfoldRangeAtomCount
  rw [publishedSymmetricRows_rowCount]

/-- **The threshold atom count, in closed form.** -/
theorem thresholdFourfoldRangeAtomCount_eq
    (contracts : PublishedContracts) (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    FourfoldRangeAggregationComposition.fourfoldRangeAtomCount
        (publishedThresholdRows contracts liveScale accuracyExponent)
        request =
      (primesUpTo
          (thresholdPrimeCutoff (selectedExactDecompositionAlgorithm contracts)
            request
            (thresholdPrimeUnionDenominator
              (selectedExactDecompositionAlgorithm contracts) request
              (fixedTargetDenominator accuracyExponent request.q)))).card *
        (2 ^ (2 * toeplitzWalkSideBits
            (canonicalGradedRank (thresholdOccurrencePopulation request)
              (thresholdOccurrenceTouchingCost request liveScale))) *
          (16 ^ 40) ^ (2 * Nat.clog 2
            (thresholdListUnionDenominator
              (selectedExactDecompositionAlgorithm contracts) request
              (fixedTargetDenominator accuracyExponent request.q) + 1))) *
        2 ^ request.q := by
  unfold FourfoldRangeAggregationComposition.fourfoldRangeAtomCount
  rw [publishedThresholdRows_rowCount]

end NearCubicWires.CanonicalFourfoldRowCountFormula
