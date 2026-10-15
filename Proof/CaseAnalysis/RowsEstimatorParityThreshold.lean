import Proof.CaseAnalysis.RowsEstimatorParitySymmetric

/-! The paper's native staircase parity circuit, with its alternating threshold top. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open Finset SupplierPipeline SourceInterfaces
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The normalized threshold gate testing whether at least `index + 1`
coordinates of `support` are true. -/
def thresholdParityBottomGate {n : ℕ} (support : Finset (Fin n))
    (index : Fin support.card) : SupportedNormalizedGate n where
  gate :=
    { weight := fun coordinate => if coordinate ∈ support then 1 else 0
      threshold := index.val + 1 }
  support := support
  zeroOutside := by
    intro coordinate hcoordinate
    simp [hcoordinate]

theorem thresholdParityBottomGate_eval {n : ℕ}
    (support : Finset (Fin n)) (index : Fin support.card)
    (input : BitInput n) :
    (thresholdParityBottomGate support index).eval input =
      decide (index.val <
        (support.filter fun coordinate => input coordinate).card) := by
  unfold thresholdParityBottomGate SupportedNormalizedGate.eval
    NormalizedThresholdGate.eval
  have hsum :
      (∑ coordinate : Fin n,
          (if coordinate ∈ support then (1 : ℤ) else 0) *
            if input coordinate then 1 else 0) =
        ((support.filter fun coordinate => input coordinate).card : ℤ) := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem_eq]
    rw [← Finset.sum_filter]
    simp
  rw [hsum]
  simp only [decide_eq_decide]
  omega

/-- Alternating weights on an initial segment sum to one exactly at odd
length, and to zero exactly at even length. -/
theorem alternatingPrefixSum (count : ℕ) :
    (∑ index ∈ Finset.range count,
        (if Even index then (1 : ℤ) else -1)) =
      if Odd count then 1 else 0 := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis]
      rcases Nat.even_or_odd count with heven | hodd
      · have hnotOdd : ¬ Odd count := Nat.not_odd_iff_even.mpr heven
        have hoddSucc : Odd (count + 1) := heven.add_one
        simp [heven, hnotOdd, hoddSucc]
      · have hnotEven : ¬ Even count := Nat.not_even_iff_odd.mpr hodd
        have hevenSucc : Even (count + 1) := hodd.add_one
        have hnotOddSucc : ¬ Odd (count + 1) :=
          Nat.not_odd_iff_even.mpr hevenSucc
        simp [hodd, hnotEven, hnotOddSucc]

/-- The alternating top threshold gate. -/
def thresholdParityTopGate (bottomCount : ℕ) :
    SupportedNormalizedGate bottomCount where
  gate :=
    { weight := fun index => if Even index.val then 1 else -1
      threshold := 1 }
  support := Finset.univ
  zeroOutside := by simp

/-- A normalized threshold-of-threshold circuit computing parity on a finite
support. -/
def normalizedThresholdParityCircuit {n : ℕ}
    (support : Finset (Fin n)) : NormalizedThresholdThresholdCircuit n where
  bottomCount := support.card
  bottom := thresholdParityBottomGate support
  top := thresholdParityTopGate support.card

theorem normalizedThresholdParityCircuit_eval {n : ℕ}
    (support : Finset (Fin n)) (input : BitInput n) :
    (normalizedThresholdParityCircuit support).eval input =
      parityOn support input := by
  let count := (support.filter fun coordinate => input coordinate).card
  have hcount : count ≤ support.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  change (thresholdParityTopGate support.card).eval
      (fun index => (thresholdParityBottomGate support index).eval input) = _
  simp_rw [thresholdParityBottomGate_eval]
  unfold thresholdParityTopGate SupportedNormalizedGate.eval
    NormalizedThresholdGate.eval
  let summand := fun index : ℕ =>
    (if Even index then (1 : ℤ) else -1) *
      if decide (index < count) then 1 else 0
  change decide ((1 : ℤ) ≤
      ∑ index : Fin support.card, summand index.val) = _
  rw [Fin.sum_univ_eq_sum_range summand support.card]
  have hsum :
      (∑ index ∈ Finset.range support.card,
          (if Even index then (1 : ℤ) else -1) *
            if decide (index < count) then 1 else 0) =
        ∑ index ∈ Finset.range count,
          (if Even index then (1 : ℤ) else -1) := by
    calc
      _ = ∑ index ∈ Finset.range count,
          (if Even index then (1 : ℤ) else -1) *
            if decide (index < count) then 1 else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono hcount)
        intro index hindexSupport hindexCount
        simp only [Finset.mem_range] at hindexSupport hindexCount
        simp [show ¬ index < count by omega]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index hindex
        simp only [Finset.mem_range] at hindex
        simp [hindex]
  rw [hsum, alternatingPrefixSum]
  rw [parityOn_eq_decide_odd_filter_card]
  dsimp only [count]
  by_cases hodd : Odd ((support.filter fun coordinate => input coordinate).card)
  · simp [hodd]
  · simp [hodd]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
