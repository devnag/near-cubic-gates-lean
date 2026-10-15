import Proof.MachineModel.ClosureCompactMetadata

/-! Exact consumer check: the arithmetic composition produces the compact
native writer's fifteen words and its actual preparation capacity. This
checks the live width/degree representation, not just word lengths. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactMetadata
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtIncidence
open RepairSource.VerifierDecoding

variable {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs] (Q w : Nat)

theorem outer_eq : outer (exactListWord gs).length n gs.length (P1Radix.bits gs) =
    RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) := by
  rw [outer,CompactSize.value_eq]
  unfold RowCachedCoordinateBounds.outer
  ring

theorem allocation_eq :
    F (exactListWord gs).length n gs.length (P1Radix.bits gs) (P1Radix.effectiveDegree gs) Q =
      P1CompactNativeAllocation.capacity gs Q := by
  unfold F RowCommonAllocation.value
  rw [outer_eq]
  unfold P1CompactNativeAllocation.capacity P1CompactRowCommonBounds.capacity
    P1CompactNativeWidth.width P1CompactRowTupleFixedCapacity.width
    RowCachedCoordinateBounds.outer p
  ring

theorem words_eq :
    words (exactListWord gs).length n gs.length (P1Radix.bits gs)
      (P1Radix.effectiveDegree gs) Q w (exactListWord gs) = P1CompactNativeMaster.words gs Q w := by
  funext i
  fin_cases i <;>
    simp [words,P1CompactNativeMaster.words,outer_eq,allocation_eq,
      p,P1CompactNativeWidth.width,P1CompactRowTupleFixedCapacity.width,
      RowCachedCoordinateBounds.inner,Nat.mul_comm]

theorem capacity_eq :
    CloseoutRowsPreparationBounds.capacity n (p (P1Radix.bits gs) (P1Radix.effectiveDegree gs) Q)
      (F (exactListWord gs).length n gs.length (P1Radix.bits gs) (P1Radix.effectiveDegree gs) Q)
      w gs.length Q = P1CompactNativeMeasured.capacity gs Q w := by
  rw [allocation_eq]
  rfl

theorem consumer_run :
    ClockJoin.ReadyRun machine
      (budget (exactListWord gs).length n gs.length (P1Radix.bits gs) (P1Radix.effectiveDegree gs) Q w)
      (input (exactListWord gs).length n gs.length (P1Radix.bits gs)
        (P1Radix.effectiveDegree gs) Q w (exactListWord gs))
      (output (exactListWord gs).length n gs.length (P1Radix.bits gs)
        (P1Radix.effectiveDegree gs) Q w (exactListWord gs)) ∧
    (∀ j, output (exactListWord gs).length n gs.length (P1Radix.bits gs)
      (P1Radix.effectiveDegree gs) Q w (exactListWord gs) (fields j) =
        P1CompactNativeMaster.words gs Q w j) ∧
    output (exactListWord gs).length n gs.length (P1Radix.bits gs)
      (P1Radix.effectiveDegree gs) Q w (exactListWord gs) 146 =
        List.replicate (P1CompactNativeMeasured.capacity gs Q w) true := by
  refine ⟨ready _ _ _ _ _ _ _ _,?_,?_⟩
  · intro j
    rw [output_fields,words_eq]
  · rw [output_capacity,capacity_eq]

theorem words_fit (i : Fin 15) :
    (P1CompactNativeMaster.words gs Q w i).length ≤ P1CompactNativeMeasured.capacity gs Q w := by
  obtain ⟨hc,hi,ho⟩ := P1CompactCloseoutRowsBankFields.cache_bounds gs
    (P1CompactNativeWidth.width gs Q) (P1CompactNativeAllocation.capacity gs Q) Q le_rfl
  have small := CloseoutRowsPreparationInput.small_fits n (P1CompactNativeWidth.width gs Q)
    (P1CompactNativeAllocation.capacity gs Q) w gs.length Q
  unfold CloseoutRowsPreparationBounds.scale at small
  change (P1CompactNativeMaster.words gs Q w i).length ≤ CloseoutRowsPreparationBounds.capacity n
    (P1CompactNativeWidth.width gs Q) (P1CompactNativeAllocation.capacity gs Q) w gs.length Q
  have hb : P1Radix.bits gs ≤ RowCachedCoordinateBounds.inner (P1Radix.bits gs) := by
    unfold RowCachedCoordinateBounds.inner
    omega
  fin_cases i <;> simp [P1CompactNativeMaster.words,UnaryTemplate.tape,CompareMachine.word,
    frame_length,SignedSortKey.binary_length]
  all_goals omega

end NearCubicWires.P1Closure.CompactMetadata
