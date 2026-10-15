import Proof.MachineModel.CanonicalSymmetricRowTableProgram
import Proof.MachineModel.CanonicalSymmetricTouchingCostProgram

/-!
# The symmetric row's live mask, executed from the typed envelope

`CanonicalSymmetricRowTableProgram` carries the greedy live-set selector only
through the abstract equation

```text
    hlive : liveMask = coordinateMask (symmetricRowLiveSet request liveScale)
```

so every row theorem is stated for *some* natural number that happens to be
that mask.  `CanonicalSymmetricTouchingCostProgram` already runs the whole
greedy conditional-expectation sweep on the envelope's support-mask tree; its
cost pipeline discards the selected mask one stage after producing it.

This module keeps that mask instead.  The first five stages are exactly the
touching-cost pipeline's; the sixth is a three-instruction projection of the
sweep's final carried state.  The result is one oracle-free program computing
`coordinateMask (symmetricRowLiveSet request liveScale)` from
`symmetricEnvelopeCode request`, so `hlive` is no longer an assumption about an
uncomputed quantity: §3 instantiates the symmetric row evaluator at the mask
this program returns, with `hlive` discharged by `rfl`.
-/

open Finset

namespace NearCubicWires.CanonicalSymmetricLiveMaskProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalFourfoldRowProducerDispatchProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalFourfoldRowTailProgram
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.CanonicalSymmetricRowCountReduction
open NearCubicWires.CanonicalSymmetricRowTableProgram
open NearCubicWires.CanonicalSymmetricSupportMaskProgram
open NearCubicWires.CanonicalSymmetricTouchingCostProgram
open NearCubicWires.CanonicalTouchingSweepProgram
open NearCubicWires.CanonicalTouchingSweepRoundProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem pair_le_pair_left (right : ℕ) {left bound : ℕ}
    (hleft : left ≤ bound) : Nat.pair left right ≤ Nat.pair bound right := by
  rcases Nat.eq_or_lt_of_le hleft with hequal | hstrict
  · rw [hequal]
  · exact (Nat.pair_lt_pair_left right hstrict).le

private theorem pair_le_pair_right (left : ℕ) {right bound : ℕ}
    (hright : right ≤ bound) : Nat.pair left right ≤ Nat.pair left bound := by
  rcases Nat.eq_or_lt_of_le hright with hequal | hstrict
  · rw [hequal]
  · exact (Nat.pair_lt_pair_right left hstrict).le

private theorem pair_le_pair {left right leftBound rightBound : ℕ}
    (hleft : left ≤ leftBound) (hright : right ≤ rightBound) :
    Nat.pair left right ≤ Nat.pair leftBound rightBound :=
  (pair_le_pair_left right hleft).trans (pair_le_pair_right leftBound hright)

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-! ## §1 The sweep's selected mask

The sweep's carried state is `pair context (pair selectedMask stepCount)`, so
keeping the selection is two `unpair` instructions. -/

/-- Keep the selected coordinate mask of a sweep's carried state. -/
def sweepSelectedMaskProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 2 0 2
  , .halt 0
  ]

@[simp] theorem sweepSelectedMaskProgram_oracleFree :
    OracleFree sweepSelectedMaskProgram := by
  rfl

def sweepSelectedMaskBits (context selectedMask stepCount : ℕ) : ℕ :=
  natBitLength (sweepCode context selectedMask stepCount)

/-- **The sweep's selected mask, executed.** -/
theorem run_sweepSelectedMaskProgram
    (inputLength context selectedMask stepCount maximumBits : ℕ)
    (hbits :
      sweepSelectedMaskBits context selectedMask stepCount ≤ maximumBits) :
    runNPOracleProgram sweepSelectedMaskProgram maximumBits 3
        (initialNPOracleState inputLength
          (sweepCode context selectedMask stepCount)) =
      some selectedMask := by
  have hcarried :
      sweepCode context selectedMask stepCount =
        Nat.pair context (Nat.pair selectedMask stepCount) := rfl
  have hinputBits :
      natBitLength (Nat.pair context (Nat.pair selectedMask stepCount)) ≤
        maximumBits := by
    rw [← hcarried]
    exact hbits
  have hstateBits :
      natBitLength (Nat.pair selectedMask stepCount) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hmaskBits : natBitLength selectedMask ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hstateBits
  rw [show (3 : ℕ) = 0 + 1 + 1 + 1 by rfl]
  rw [run_unpairRight_instruction
    (value := Nat.pair selectedMask stepCount)
    (by rfl) rfl
    (by simp [initialNPOracleState, sweepCode])
    hstateBits]
  rw [run_unpairLeft_instruction
    (value := selectedMask)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hmaskBits]
  exact run_halt_instruction (fuel := 0) (value := selectedMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmaskBits

/-! ## §2 The live mask, executed from the typed envelope

Six linked stages: the pool's support-mask tree, the sweep's live budget, the
sweep's public input, the counted round call itself, and §1. -/

/-- **The symmetric row's live-mask program.** -/
def symmetricLiveMaskProgram (liveScale : ℕ) : NPOracleProgram :=
  linkPrograms symmetricOccurrenceSupportMaskProgram
    (linkPrograms (scalePairProgram 0)
      (linkPrograms (preserveRightProgram (liveCountProgram liveScale))
        (linkPrograms roundInputProgram
          (linkPrograms (roundCallProgram touchingSweepRoundProgram)
            sweepSelectedMaskProgram))))

theorem symmetricLiveMaskProgram_oracleFree (liveScale : ℕ) :
    OracleFree (symmetricLiveMaskProgram liveScale) :=
  oracleFree_linkPrograms symmetricOccurrenceSupportMaskProgram_oracleFree
    (oracleFree_linkPrograms (scalePairProgram_oracleFree 0)
      (oracleFree_linkPrograms
        (preserveRightProgram_oracleFree (liveCountProgram liveScale)
          (liveCountProgram_oracleFree liveScale))
        (oracleFree_linkPrograms roundInputProgram_oracleFree
          (oracleFree_linkPrograms
            (roundCallProgram_oracleFree touchingSweepRoundProgram_oracleFree)
            sweepSelectedMaskProgram_oracleFree))))

/-- The sweep's final step budget, named once. -/
def symmetricSweepResidualBudget (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  (sweepFold (occurrenceSupport (symmetricFourfoldOccurrences request))
    (List.finRange request.q)
    ((∅ : Finset (Fin request.q)),
      normalizedLiveCount request.q liveScale)).2

def symmetricLiveMaskFuel (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  linkFuel
      (linkPrograms (scalePairProgram 0)
        (linkPrograms (preserveRightProgram (liveCountProgram liveScale))
          (linkPrograms roundInputProgram
            (linkPrograms (roundCallProgram touchingSweepRoundProgram)
              sweepSelectedMaskProgram))))
      (symmetricOccurrenceSupportMaskFuel request)
    (linkFuel
        (linkPrograms (preserveRightProgram (liveCountProgram liveScale))
          (linkPrograms roundInputProgram
            (linkPrograms (roundCallProgram touchingSweepRoundProgram)
              sweepSelectedMaskProgram)))
        3
      (linkFuel
          (linkPrograms roundInputProgram
            (linkPrograms (roundCallProgram touchingSweepRoundProgram)
              sweepSelectedMaskProgram))
          (preserveRightFuel (liveCountFuel liveScale request.q))
        (linkFuel
            (linkPrograms (roundCallProgram touchingSweepRoundProgram)
              sweepSelectedMaskProgram)
            8
          (linkFuel sweepSelectedMaskProgram
            (roundCallFuel touchingSweepRoundProgram
              (touchingSweepCalleeFuel (symmetricFourfoldOccurrences request))
              (touchingSweepStep (symmetricFourfoldOccurrences request))
              (sweepStateCode
                (touchingSweepContext (symmetricFourfoldOccurrences request)
                  request.q)
                ((∅ : Finset (Fin request.q)),
                  normalizedLiveCount request.q liveScale))
              request.q)
            3))))

def symmetricLiveMaskStageBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List ℕ :=
  [ 1
  , natBitLength request.q
  , symmetricOccurrenceSupportMaskBits request
  , scalePairBits 0 (symmetricPoolMasksTree request)
  , preserveRightBits (liveCountBits liveScale request.q) 0
      (symmetricPoolMasksTree request)
      (normalizedLiveCount request.q liveScale)
  , roundInputBits request.q (symmetricPoolMasksTree request)
      (normalizedLiveCount request.q liveScale)
  , natBitLength
      (Nat.pair
        (sweepCarriedBound
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          request.q (normalizedLiveCount request.q liveScale))
        request.q)
  , natBitLength
      (Nat.pair
        (Nat.pair
          (sweepCarriedBound
            (touchingSweepContext (symmetricFourfoldOccurrences request)
              request.q)
            request.q (normalizedLiveCount request.q liveScale))
          request.q)
        (sweepCarriedBound
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          request.q (normalizedLiveCount request.q liveScale)))
  , sweepSelectedMaskBits
      (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
      (coordinateMask
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))
      (symmetricSweepResidualBudget liveScale request)
  ]

/-- The pre-finite-envelope stage ledger, retained as a compatibility formula. -/
def symmetricLiveMaskLegacyBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  (symmetricLiveMaskStageBits liveScale request).foldr max 1

/-- The public live-mask width includes every bounded invocation of its round
callee in addition to the legacy stage ledger. -/
def symmetricLiveMaskBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  max (symmetricLiveMaskLegacyBits liveScale request)
    (symmetricTouchingRoundSupBits liveScale request)

theorem symmetricLiveMaskLegacyBits_le_bits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    symmetricLiveMaskLegacyBits liveScale request ≤
      symmetricLiveMaskBits liveScale request := by
  exact le_max_left _ _

theorem touchingSweepRoundBits_le_symmetricLiveMaskBits (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (selected : Finset (Fin request.q)) (stepCount counter : ℕ)
    (hcounter : counter + 1 ≤ request.q)
    (hstep : stepCount ≤ normalizedLiveCount request.q liveScale) :
    touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
        stepCount (request.q - (counter + 1)) counter ≤
      symmetricLiveMaskBits liveScale request := by
  let point : SymmetricTouchingRoundIndex liveScale request :=
    { selected := selected
      stepCount := ⟨stepCount, Nat.lt_succ_iff.mpr hstep⟩
      counter := ⟨counter, Nat.lt_iff_add_one_le.mpr hcounter⟩ }
  exact (symmetricTouchingRoundBitsAt_le_supBits liveScale request point).trans
    (le_max_right _ _)

set_option maxHeartbeats 2000000 in
-- Six linked stages at one shared register width; the sweep controller's four
-- width premises come from the same carried-state envelope the touching-cost
-- pipeline uses, and only the round callee's own width premise stays
-- quantified.
/-- **The symmetric row's live mask, executed from the typed envelope.**  This
is the greedy conditional-expectation sweep's own selection, so the mask
`CanonicalSymmetricRowTableProgram` carries in `hlive` is now a computed
quantity. -/
theorem run_symmetricLiveMaskProgram (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (maximumBits : ℕ)
    (hbits : symmetricLiveMaskBits liveScale request ≤ maximumBits)
    (hroundBits : ∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
      counter + 1 ≤ request.q →
      stepCount ≤ normalizedLiveCount request.q liveScale →
      touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
          stepCount (request.q - (counter + 1)) counter ≤
        maximumBits) :
    runNPOracleProgram (symmetricLiveMaskProgram liveScale) maximumBits
        (symmetricLiveMaskFuel liveScale request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some
        (coordinateMask
          (normalizedLiveSet (symmetricFourfoldOccurrences request)
            liveScale)) := by
  have bits_of_member {value : ℕ}
      (hvalue : value ∈ symmetricLiveMaskStageBits liveScale request) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue)
      ((symmetricLiveMaskLegacyBits_le_bits liveScale request).trans hbits)
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hlength : natBitLength request.q ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hmaskBits :
      symmetricOccurrenceSupportMaskBits request ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hscaleBits :
      scalePairBits 0 (symmetricPoolMasksTree request) ≤ maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hpreserveBits :
      preserveRightBits (liveCountBits liveScale request.q) 0
          (symmetricPoolMasksTree request)
          (normalizedLiveCount request.q liveScale) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hroundInputBits :
      roundInputBits request.q (symmetricPoolMasksTree request)
          (normalizedLiveCount request.q liveScale) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hcarriedEnvelopeBits :
      natBitLength
          (Nat.pair
            (sweepCarriedBound
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              request.q (normalizedLiveCount request.q liveScale))
            request.q) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hreturnEnvelopeBits :
      natBitLength
          (Nat.pair
            (Nat.pair
              (sweepCarriedBound
                (touchingSweepContext (symmetricFourfoldOccurrences request)
                  request.q)
                request.q (normalizedLiveCount request.q liveScale))
              request.q)
            (sweepCarriedBound
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              request.q (normalizedLiveCount request.q liveScale))) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hselectBits :
      sweepSelectedMaskBits
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          (coordinateMask
            (normalizedLiveSet (symmetricFourfoldOccurrences request)
              liveScale))
          (symmetricSweepResidualBudget liveScale request) ≤
        maximumBits := by
    apply bits_of_member
    simp [symmetricLiveMaskStageBits]
  have hcontext :
      touchingSweepContext (symmetricFourfoldOccurrences request) request.q =
        Nat.pair request.q (symmetricPoolMasksTree request) := rfl
  have hinitialState :
      sweepStateCode
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          ((∅ : Finset (Fin request.q)),
            normalizedLiveCount request.q liveScale) =
        sweepCode (Nat.pair request.q (symmetricPoolMasksTree request)) 0
          (normalizedLiveCount request.q liveScale) := by
    unfold sweepStateCode
    rw [← hcontext, coordinateMask_empty]
  have hsweepInputBits :
      natBitLength
          (roundCallInput request.q
            (sweepStateCode
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              ((∅ : Finset (Fin request.q)),
                normalizedLiveCount request.q liveScale))) ≤
        maximumBits := by
    rw [hinitialState]
    refine le_trans ?_ hroundInputBits
    exact Nat.le_max_right _ _
  have hsweepCarriedBits : ∀ carried counter,
      SweepReachable request.q
        (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
        (normalizedLiveCount request.q liveScale) carried counter →
      natBitLength (Nat.pair carried counter) ≤ maximumBits := by
    intro carried counter hreachable
    obtain ⟨hcounter, selected, stepCount, hstepCount, hcarried⟩ := hreachable
    rw [hcarried]
    refine bits_of_le ?_ hcarriedEnvelopeBits
    exact pair_le_pair
      (sweepStateCode_le_sweepCarriedBound
        (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
        selected hstepCount)
      hcounter
  have hsweepReturnBits : ∀ carried counter,
      SweepReachable request.q
        (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
        (normalizedLiveCount request.q liveScale) carried (counter + 1) →
      natBitLength
          (Nat.pair (Nat.pair carried (counter + 1))
            (touchingSweepStep (symmetricFourfoldOccurrences request) carried
              (counter + 1))) ≤
        maximumBits := by
    intro carried counter hreachable
    obtain ⟨hcounter, selected, stepCount, hstepCount, hcarried⟩ := hreachable
    rw [hcarried, touchingSweepStep_sweepStateCode
      (symmetricFourfoldOccurrences request) selected stepCount (counter + 1)]
    have hnextStep :
        (sweepRound (occurrenceSupport (symmetricFourfoldOccurrences request))
            ((List.finRange request.q).drop (request.q - (counter + 1)))
            (selected, stepCount)).2 ≤
          normalizedLiveCount request.q liveScale :=
      le_trans
        (sweepRound_snd_le
          (occurrenceSupport (symmetricFourfoldOccurrences request))
          ((List.finRange request.q).drop (request.q - (counter + 1)))
          (selected, stepCount))
        hstepCount
    refine bits_of_le ?_ hreturnEnvelopeBits
    refine pair_le_pair
      (pair_le_pair
        (sweepStateCode_le_sweepCarriedBound
          (touchingSweepContext (symmetricFourfoldOccurrences request)
            request.q)
          selected hstepCount)
        hcounter)
      ?_
    exact sweepStateCode_le_sweepCarriedBound
      (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
      (sweepRound (occurrenceSupport (symmetricFourfoldOccurrences request))
        ((List.finRange request.q).drop (request.q - (counter + 1)))
        (selected, stepCount)).1
      hnextStep
  have hstageOne :
      runNPOracleProgram symmetricOccurrenceSupportMaskProgram maximumBits
          (symmetricOccurrenceSupportMaskFuel request)
          (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
        some (symmetricPoolMasksTree request) :=
    run_symmetricOccurrenceSupportMaskProgram request maximumBits hmaskBits
  have hstageTwo :
      runNPOracleProgram (scalePairProgram 0) maximumBits 3
          (initialNPOracleState request.q
            (symmetricPoolMasksTree request)) =
        some (Nat.pair 0 (symmetricPoolMasksTree request)) :=
    run_scalePairProgram request.q 0 (symmetricPoolMasksTree request)
      maximumBits hscaleBits
  have hstageThree :
      runNPOracleProgram (preserveRightProgram (liveCountProgram liveScale))
          maximumBits
          (preserveRightFuel (liveCountFuel liveScale request.q))
          (initialNPOracleState request.q
            (Nat.pair 0 (symmetricPoolMasksTree request))) =
        some
          (Nat.pair (normalizedLiveCount request.q liveScale)
            (symmetricPoolMasksTree request)) :=
    run_bits_mono
      (run_preserveRightProgram (liveCountProgram liveScale) request.q
        (liveCountBits liveScale request.q)
        (liveCountFuel liveScale request.q) 0
        (symmetricPoolMasksTree request)
        (normalizedLiveCount request.q liveScale)
        (run_liveCountProgram liveScale request.q 0
          (liveCountBits liveScale request.q) (le_refl _)))
      hpreserveBits
  have hstageFour :
      runNPOracleProgram roundInputProgram maximumBits 8
          (initialNPOracleState request.q
            (Nat.pair (normalizedLiveCount request.q liveScale)
              (symmetricPoolMasksTree request))) =
        some
          (roundCallInput request.q
            (sweepStateCode
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              ((∅ : Finset (Fin request.q)),
                normalizedLiveCount request.q liveScale))) := by
    rw [hinitialState]
    exact run_roundInputProgram request.q (symmetricPoolMasksTree request)
      (normalizedLiveCount request.q liveScale) maximumBits hroundInputBits
  have hstageFive :
      runNPOracleProgram (roundCallProgram touchingSweepRoundProgram)
          maximumBits
          (roundCallFuel touchingSweepRoundProgram
            (touchingSweepCalleeFuel (symmetricFourfoldOccurrences request))
            (touchingSweepStep (symmetricFourfoldOccurrences request))
            (sweepStateCode
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              ((∅ : Finset (Fin request.q)),
                normalizedLiveCount request.q liveScale))
            request.q)
          (initialNPOracleState request.q
            (roundCallInput request.q
              (sweepStateCode
                (touchingSweepContext (symmetricFourfoldOccurrences request)
                  request.q)
                ((∅ : Finset (Fin request.q)),
                  normalizedLiveCount request.q liveScale)))) =
        some
          (sweepCode
            (touchingSweepContext (symmetricFourfoldOccurrences request)
              request.q)
            (coordinateMask
              (normalizedLiveSet (symmetricFourfoldOccurrences request)
                liveScale))
            (symmetricSweepResidualBudget liveScale request)) :=
    run_touchingSweepSelectProgram (symmetricFourfoldOccurrences request)
      request.q (normalizedLiveCount request.q liveScale) maximumBits
      hpositive hsweepInputBits hsweepCarriedBits hsweepReturnBits hroundBits
  have hstageSix :
      runNPOracleProgram sweepSelectedMaskProgram maximumBits 3
          (initialNPOracleState request.q
            (sweepCode
              (touchingSweepContext (symmetricFourfoldOccurrences request)
                request.q)
              (coordinateMask
                (normalizedLiveSet (symmetricFourfoldOccurrences request)
                  liveScale))
              (symmetricSweepResidualBudget liveScale request))) =
        some
          (coordinateMask
            (normalizedLiveSet (symmetricFourfoldOccurrences request)
              liveScale)) :=
    run_sweepSelectedMaskProgram request.q
      (touchingSweepContext (symmetricFourfoldOccurrences request) request.q)
      (coordinateMask
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))
      (symmetricSweepResidualBudget liveScale request) maximumBits hselectBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree
        (run_linkPrograms hpositive hlength hstageFour
          (run_linkPrograms hpositive hlength hstageFive hstageSix))))

/-! ## §3 The row evaluator at the computed mask

Instantiating `CanonicalSymmetricRowTableProgram` at the mask §2 returns
discharges `hlive` by `rfl`, so the symmetric row evaluator's remaining
premises are exactly the two producer contracts. -/

/-- The mask §2 returns, named as the row table's live mask. -/
def symmetricRowLiveMask
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) : ℕ :=
  coordinateMask (symmetricRowLiveSet request liveScale)

theorem run_symmetricLiveMaskProgram_rowMask (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (maximumBits : ℕ)
    (hbits : symmetricLiveMaskBits liveScale request ≤ maximumBits)
    (hroundBits : ∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
      counter + 1 ≤ request.q →
      stepCount ≤ normalizedLiveCount request.q liveScale →
      touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
          stepCount (request.q - (counter + 1)) counter ≤
        maximumBits) :
    runNPOracleProgram (symmetricLiveMaskProgram liveScale) maximumBits
        (symmetricLiveMaskFuel liveScale request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricRowLiveMask request liveScale) :=
  run_symmetricLiveMaskProgram liveScale request maximumBits hbits hroundBits

/-- **The symmetric fork row evaluator at the computed live mask.**  Exactly
`run_symmetricRowForkEvaluatorProgram` with `hlive` discharged: the mask is the
one `symmetricLiveMaskProgram` returns. -/
theorem run_symmetricRowForkEvaluatorProgram_computedMask
    (requestProgram polynomialProgram : NPOracleProgram)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale accuracyExponent rowIndex : ℕ) (input : BitInput request.q)
    (maximumBits tableBits polynomialBits requestFuel polynomialFuel : ℕ)
    (htableBits :
      symmetricRowTableStageBits request liveScale input
          (encodeBitInput input) (symmetricRowLiveMask request liveScale) ≤
        tableBits)
    (hbits :
      structuralForkRowEvaluatorBits request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)
          tableBits polynomialBits
          (symmetricRowResidualAssignment request liveScale input)
          (symmetricRowPolynomial request liveScale accuracyExponent rowIndex
            input) ≤
        maximumBits)
    (hrequest :
      runNPOracleProgram requestProgram tableBits requestFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (residualAssignmentTableInput (symmetricRowOccurrences request)
            (encodeBitInput input) (symmetricRowLiveMask request liveScale)))
    (hpolynomial :
      runNPOracleProgram polynomialProgram polynomialBits polynomialFuel
          (initialNPOracleState request.q
            (symmetricFourfoldRowTailHandoff algorithm request rowIndex
              input)) =
        some
          (encodedStructuralGF2
            (symmetricRowPolynomial request liveScale accuracyExponent
              rowIndex input))) :
    runNPOracleProgram
        (symmetricRowForkEvaluatorProgram requestProgram polynomialProgram)
        maximumBits
        (symmetricRowForkEvaluatorFuel requestProgram polynomialProgram
          request liveScale accuracyExponent rowIndex input requestFuel
          polynomialFuel (symmetricRowLiveMask request liveScale))
        (initialNPOracleState request.q
          (symmetricFourfoldRowTailHandoff algorithm request rowIndex input)) =
      some
        (boolCode
          (evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
            (symmetricFourfoldRowRequest request rowIndex input))) :=
  run_symmetricRowForkEvaluatorProgram requestProgram polynomialProgram
    algorithm request liveScale accuracyExponent rowIndex input
    (symmetricRowLiveMask request liveScale) maximumBits tableBits
    polynomialBits requestFuel polynomialFuel rfl htableBits hbits hrequest
    hpolynomial

end NearCubicWires.CanonicalSymmetricLiveMaskProgram
